use std::collections::{BTreeMap, VecDeque};

use crate::frontend::{
    ast::{
        Block, Expression, ExpressionKind, FunctionDefinition, FunctionParameter, Local, LocalKind,
        Module, NodeId, QualifiedIdentifier, Statement, StatementKind, Type, TypeKind,
    },
    intern::InternedSymbol,
    lexer::Span,
};

/// A map between AST identifier nodes and their definitions
#[derive(Debug)]
pub struct ModuleResolutionMap {
    /// Maps the usage of value identifiers (variable names) to their point of
    /// original definition
    pub value_name_resolutions: BTreeMap<NodeId, ValueNameResolution>,
    /// Maps the usage of type identifiers to their point of original definition
    pub type_name_resolutions: BTreeMap<NodeId, TypeNameResolution>,
}

/// A resolved value name
///
/// Can be either a local variable binding, function parameter binding, or a user defined function
#[derive(Debug, Clone)]
pub enum ValueNameResolution {
    Local(NodeId),
    Parameter(NodeId),
    Definition(ValueDefinitionKind, DefinitionId),
}

#[derive(Debug, Clone)]
pub enum ValueDefinitionKind {
    Function,
    Constant,
    Static,
}

/// A resolved type name
///
/// Can either be a built in primitive type name or a reference to a user
/// defined type
#[derive(Debug, Clone)]
/// A data structure to assist in traversing AST scopes within a specific
/// namespace (values or types)
pub enum TypeNameResolution {
    Definition(TypeDefinitionKind, DefinitionId),
}

#[derive(Debug, Clone)]
pub enum TypeDefinitionKind {
    Struct,
    Enum,
    Union,
    Alias,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DefinitionId {
    BuiltIn { id: u32 },
    Module { module_id: u32, node_id: NodeId },
}

impl DefinitionId {
    pub const BUILT_IN_PRINTLN: Self = Self::BuiltIn { id: 0 };

    pub fn new_module(module_id: u32, node_id: NodeId) -> Self {
        Self::Module { module_id, node_id }
    }
}

/// AST Module name resolver
///
/// Traverses the AST for a module and creates a map from type and value names
/// to their definitions within the source code.
#[derive(Debug)]
pub struct Resolver<'module> {
    module: &'module Module<'module>,
    value_scope_stack: ScopeStack<ValueNameResolution>,
    type_scope_stack: ScopeStack<TypeNameResolution>,
    resolutions: ModuleResolutionMap,
}

impl<'module> Resolver<'module> {
    /// Resolves all names within a module in 2 steps.
    ///
    /// The first step resolves imports and locates all the definitions of
    /// custom types and functions. These imports and custom types are then
    /// bound in the global value and type scopes
    ///
    /// The second step traverses the AST and makes sure any references to types
    /// or values are defined in this module's scope or are imported. It also
    /// keeps track of function parameters and local variables to make sure all
    /// identifiers are valid. Field and method accesses are not checked at this
    /// stage and are resolved during module type checking.
    pub fn resolve_names(module: &'module Module) -> ModuleResolutionMap {
        let mut resolver = Self {
            module,
            value_scope_stack: ScopeStack::new(),
            type_scope_stack: ScopeStack::new(),
            resolutions: ModuleResolutionMap {
                value_name_resolutions: BTreeMap::new(),
                type_name_resolutions: BTreeMap::new(),
            },
        };

        resolver.bind_built_ins();
        // TODO: bind imports
        // TODO: bind type aliases
        // TODO: bind custom types (structs, unions, enums, etc)
        resolver.bind_function_definitions();

        for function in &resolver.module.function_definitions {
            resolver.resolve_function_definition(function);
        }

        // TODO: warn about unused imports

        resolver.resolutions
    }

    fn bind_built_ins(&mut self) {
        self.value_scope_stack.add_global_binding(
            InternedSymbol::new("println"),
            ValueNameResolution::Definition(
                ValueDefinitionKind::Function,
                DefinitionId::BUILT_IN_PRINTLN,
            ),
        )
    }

    /// Adds all the function definitions from the module to the module's outer
    /// scope
    fn bind_function_definitions(&mut self) {
        for function in &self.module.function_definitions {
            if self
                .value_scope_stack
                .get_global_binding(function.signature.name.symbol)
                .is_some()
            {
                self.report_duplicate_binding(function.signature.name.span)
            }

            self.value_scope_stack.add_global_binding(
                function.signature.name.symbol,
                ValueNameResolution::Definition(
                    ValueDefinitionKind::Function,
                    DefinitionId::new_module(self.module.id, function.id),
                ),
            )
        }
    }

    /// Resolves all names within a function definition
    fn resolve_function_definition(&mut self, function: &FunctionDefinition) {
        self.value_scope_stack.push_shallow_scope();

        // Resolve types of parameters and bind parameter names into the scope

        for parameter in &function.signature.parameters.parameters {
            self.resolve_function_parameter(parameter);
        }

        // Resolve return type to make sure it exists

        if let Some(return_type) = &function.signature.return_type {
            self.resolve_type(return_type);
        }

        // Go through the statements in the body to bind locals and resolve identifiers within expressions

        self.resolve_block(&function.body);

        self.value_scope_stack.pop_shallow_scope();
    }

    fn report_duplicate_binding(&self, offending_span: Span) -> ! {
        eprintln!(
            "Conflicting definition for identifier `{}` ({}:{}:{})",
            self.module.source_file.value_of_span(offending_span),
            self.module.source_file.origin,
            self.module
                .source_file
                .row_for_position(offending_span.start),
            self.module
                .source_file
                .column_for_position(offending_span.start)
        );
        self.module.source_file.highlight_span(offending_span);
        // TODO: show where the original binding was defined
        // TODO: recover from this error and keep moving
        std::process::exit(1);
    }

    fn report_unresolved(&self, offending_span: Span) -> ! {
        eprintln!(
            "Unresolved name for identifier `{}` ({}:{}:{})",
            self.module.source_file.value_of_span(offending_span),
            self.module.source_file.origin,
            self.module
                .source_file
                .row_for_position(offending_span.start),
            self.module
                .source_file
                .column_for_position(offending_span.start)
        );
        self.module.source_file.highlight_span(offending_span);
        // TODO: recover from this error and keep moving
        std::process::exit(1);
    }

    fn resolve_function_parameter(&mut self, parameter: &FunctionParameter) {
        // Check that name is not already bound in the current scope

        if self
            .value_scope_stack
            .get_shallow_binding(parameter.name.symbol)
            .is_some()
        {
            self.report_duplicate_binding(parameter.name.span);
        }

        // Add the binding for the parameter name

        self.value_scope_stack.add_shallow_binding(
            parameter.name.symbol,
            ValueNameResolution::Parameter(parameter.id),
        );

        // Resolve the parameter type

        self.resolve_type(&parameter.ty);
    }

    fn resolve_type(&mut self, ty: &Type) {
        match &ty.kind {
            TypeKind::QualifiedIdentifier(qualified_ident) => {
                // There are 2 possibilities here:
                //   1) The identifier only has one segment and must be a
                //      primitive or local/imported custom type (alias, struct, enum,
                //      etc.). This can be resolved by checking if it's a primitive
                //      and then checking the global scope if that fails
                //  2) The identifier has more than one segment and we must start
                //      from the first and resolve from there

                // Case 1
                if let [ident] = qualified_ident.segments.as_slice() {
                    // Resolve from the global scope
                    let Some(resolution) = self.type_scope_stack.get_global_binding(ident.symbol)
                    else {
                        self.report_unresolved(ident.span);
                    };

                    self.resolutions
                        .type_name_resolutions
                        .insert(qualified_ident.id, resolution.clone());
                }

                // Case 2
                todo!("Resolve type identifier by traversing qualified identifier segments")
            }
            TypeKind::Pointer(ty) => self.resolve_type(ty),
            TypeKind::Slice(ty) => self.resolve_type(ty),
            TypeKind::Array { ty, .. } => self.resolve_type(ty),
            // Nothing needs to be done to resolve these types
            TypeKind::Primitive(_) | TypeKind::Str | TypeKind::CStr | TypeKind::Any => {}
        }
    }

    fn resolve_block(&mut self, block: &Block) {
        self.value_scope_stack.push_shallow_scope();

        for statement in &block.statements {
            self.resolve_statement(statement)
        }

        self.value_scope_stack.pop_shallow_scope();
    }

    fn resolve_statement(&mut self, statement: &Statement) {
        match &statement.kind {
            StatementKind::Local(local) => self.resolve_local(local),
            StatementKind::BareExpr(expression) | StatementKind::SemiExpr(expression) => {
                self.resolve_expression(expression)
            }
            StatementKind::Empty => {}
        }
    }

    fn resolve_local(&mut self, local: &Local) {
        // Check the expression first (we don't want this local's name to be
        // available within the initialization expression)
        if let LocalKind::Initialization(initialization_expression) = &local.kind {
            self.resolve_expression(initialization_expression);
        }

        // Check that name is not already bound in the current scope (allowed to
        // be bound in higher scopes and rebound in the current scope)
        if self
            .value_scope_stack
            .get_shallow_binding(local.name.symbol)
            .is_some()
        {
            self.report_duplicate_binding(local.name.span);
        }

        // Add the binding for the local name

        self.value_scope_stack
            .add_shallow_binding(local.name.symbol, ValueNameResolution::Local(local.id));

        // Resolve the type if one was given explicitly

        if let Some(ty) = &local.ty {
            self.resolve_type(ty);
        }
    }

    fn resolve_expression(&mut self, expression: &Expression) {
        match &expression.kind {
            ExpressionKind::QualifiedIdentifier(qualified_ident) => {
                self.resolve_identifier(qualified_ident)
            }
            ExpressionKind::Grouping(expression) => self.resolve_expression(expression),
            ExpressionKind::Block(block) => self.resolve_block(block),
            ExpressionKind::FunctionCall { target, arguments } => {
                self.resolve_expression(target);

                for argument in &arguments.arguments {
                    self.resolve_expression(argument)
                }
            }
            ExpressionKind::Binary {
                lhs,
                operator: _,
                rhs,
            } => {
                self.resolve_expression(lhs);
                self.resolve_expression(rhs);
            }
            ExpressionKind::Unary {
                operator: _,
                operand,
            } => self.resolve_expression(operand),
            ExpressionKind::Cast { expression, ty } => {
                self.resolve_expression(expression);
                self.resolve_type(ty);
            }
            ExpressionKind::If {
                condition,
                positive,
                negative,
            } => {
                self.resolve_expression(condition);
                self.resolve_block(positive);

                if let Some(negative) = negative {
                    self.resolve_expression(negative);
                }
            }
            ExpressionKind::While { condition, block } => {
                self.resolve_expression(condition);
                self.resolve_block(block);
            }
            ExpressionKind::Assignment { lhs, rhs } => {
                self.resolve_expression(rhs);
                self.resolve_expression(lhs);
            }
            ExpressionKind::OperatorAssignment {
                operator: _,
                lhs,
                rhs,
            } => {
                self.resolve_expression(rhs);
                self.resolve_expression(lhs);
            }
            ExpressionKind::Return(expression) => {
                if let Some(expression) = expression {
                    self.resolve_expression(expression)
                }
            }
            ExpressionKind::Literal(_) | ExpressionKind::Break | ExpressionKind::Continue => {}
        }
    }

    /// Resolves a value identifier (within an expression)
    fn resolve_identifier(&mut self, qualified_ident: &QualifiedIdentifier) {
        // There are 2 possibilities here:
        //   1) The ident has no qualifier and it refers to a local, function
        //      parameter, or local/imported definition
        //   2) The ident has a qualifier so we should start at the first segment
        //      and resolve from there

        // Case 1
        if let [ident] = qualified_ident.segments.as_slice() {
            let Some(resolution) = self.value_scope_stack.get_binding(ident.symbol) else {
                self.report_unresolved(ident.span);
            };

            self.resolutions
                .value_name_resolutions
                .insert(qualified_ident.id, resolution.clone());

            return;
        }

        // Case 2
        todo!("Resolve value identifier by traversing qualified identifier segments")
    }
}

/// A data structure to assist in traversing AST scopes within a specific
/// namespace (values or types)
#[derive(Debug)]
struct ScopeStack<R> {
    global_scope: BTreeMap<InternedSymbol, R>,
    stack: VecDeque<BTreeMap<InternedSymbol, R>>,
}

impl<R> ScopeStack<R> {
    fn new() -> Self {
        Self {
            global_scope: BTreeMap::new(),
            stack: VecDeque::new(),
        }
    }

    /// Creates a new block or function scope
    fn push_shallow_scope(&mut self) {
        self.stack.push_back(BTreeMap::new());
    }

    /// Destroys the current block or function scope
    fn pop_shallow_scope(&mut self) {
        assert!(
            !self.stack.is_empty(),
            "Attempted to pop a shallow scope from the global context"
        );

        self.stack.pop_back();
    }

    /// Looks for a binding only within the current (most nested) scope
    fn get_shallow_binding(&self, symbol: InternedSymbol) -> Option<&R> {
        assert!(
            !self.stack.is_empty(),
            "Tried to get a shallow binding from the global context"
        );

        let shallow_scope = self.stack.back().unwrap();

        shallow_scope.get(&symbol)
    }

    /// Adds a binding only within the current (most nested) scope
    fn add_shallow_binding(&mut self, symbol: InternedSymbol, name_resolution: R) {
        assert!(
            !self.stack.is_empty(),
            "Tried to add a shallow binding in the global context"
        );

        let shallow_scope = self.stack.back_mut().unwrap();

        shallow_scope.insert(symbol, name_resolution);
    }

    /// Gets a binding from the global scope
    fn get_global_binding(&self, symbol: InternedSymbol) -> Option<&R> {
        self.global_scope.get(&symbol)
    }

    /// Adds a binding into the global scope which is accessible from all
    /// shallow scopes
    fn add_global_binding(&mut self, symbol: InternedSymbol, name_resolution: R) {
        self.global_scope.insert(symbol, name_resolution);
    }

    /// Traverses the scope stack from back to front looking for bindings before
    /// checking the global scope.
    fn get_binding(&self, symbol: InternedSymbol) -> Option<&R> {
        for scope in self.stack.iter().rev() {
            if let Some(binding) = scope.get(&symbol) {
                return Some(binding);
            }
        }

        self.global_scope.get(&symbol)
    }
}
