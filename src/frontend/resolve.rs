use std::collections::{BTreeMap, VecDeque};

use strum::{EnumIter, EnumString, IntoEnumIterator};

use super::{
    ast::{
        Block, Expression, ExpressionKind, FunctionDefinition, FunctionParameter, InternedSymbol,
        Local, LocalKind, Module, NodeId, QualifiedIdentifier, Statement, StatementKind, Type,
        TypeKind,
    },
    lexer::Span,
};

#[derive(Debug)]
pub struct Resolver<'module> {
    module: &'module Module<'module>,
    value_scope_stack: ScopeStack<ValueNameResolution>,
    type_scope_stack: ScopeStack<TypeNameResolution>,
    result: ResolutionResult,
}

impl<'module> Resolver<'module> {
    pub fn resolve_names(module: &'module Module) -> ResolutionResult {
        let mut resolver = Self {
            module,
            type_scope_stack: ScopeStack::new(),
            value_scope_stack: ScopeStack::new(),
            result: ResolutionResult {
                value_name_resolution_map: BTreeMap::new(),
                type_name_resolution_map: BTreeMap::new(),
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

        resolver.result
    }

    fn bind_built_ins(&mut self) {
        self.value_scope_stack.add_global_binding(
            InternedSymbol::new("println"),
            ValueNameResolution::Definition(ValueDefinitionKind::Function, DefinitionId::BuiltIn),
        )
    }

    /// Adds all the function definitions from the module to the module's outer
    /// scope
    fn bind_function_definitions(&mut self) {
        for function in &self.module.function_definitions {
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
            "Conflicting binding for identifier `{}` ({}:{}:{})",
            self.module.source_file.value_of_span(offending_span),
            self.module.source_file.origin,
            self.module
                .source_file
                .line_number_for_position(offending_span.start),
            self.module
                .source_file
                .column_for_position(offending_span.start)
        );
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
                .line_number_for_position(offending_span.start),
            self.module
                .source_file
                .column_for_position(offending_span.start)
        );
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
                    // Try and resolve it as a primitive
                    if let Ok(kind) = ident.symbol.value().parse() {
                        self.result
                            .type_name_resolution_map
                            .insert(qualified_ident.id, TypeNameResolution::Primitive(kind));

                        return;
                    }

                    // Resolve from the global scope
                    let Some(resolution) = self.type_scope_stack.get_global_binding(ident.symbol)
                    else {
                        self.report_unresolved(ident.span);
                    };

                    self.result
                        .type_name_resolution_map
                        .insert(qualified_ident.id, resolution.clone());
                }

                // Case 2
                todo!("Resolve type identifier by traversing qualified identifier segments")
            }
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
            ExpressionKind::FunctionCall {
                function,
                arguments,
            } => {
                self.resolve_expression(function);

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

            self.result
                .value_name_resolution_map
                .insert(qualified_ident.id, resolution.clone());

            return;
        }

        // Case 2
        todo!("Resolve value identifier by traversing qualified identifier segments")
    }
}

#[derive(Debug)]
pub struct ResolutionResult {
    /// Maps the usage of value identifiers (variable names) to their point of
    /// original definition
    pub value_name_resolution_map: BTreeMap<NodeId, ValueNameResolution>,
    /// Maps the usage of type identifiers to their point of original definition
    pub type_name_resolution_map: BTreeMap<NodeId, TypeNameResolution>,
}

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

#[derive(Debug, Clone)]
pub enum TypeNameResolution {
    Definition(TypeDefinitionKind, DefinitionId),
    Primitive(PrimitiveKind),
}

#[derive(Debug, Clone)]
pub enum ValueNameResolution {
    Definition(ValueDefinitionKind, DefinitionId),
    Local(NodeId),
    Parameter(NodeId),
}

#[derive(Debug, Clone)]
pub enum TypeDefinitionKind {
    Struct,
    Enum,
    Union,
    Alias,
}

#[derive(Debug, Clone)]
pub enum ValueDefinitionKind {
    Function,
    Constant,
    Static,
}

#[derive(Debug, Clone)]
pub enum DefinitionId {
    BuiltIn,
    Module { module_id: u32, node_id: NodeId },
}

impl DefinitionId {
    fn new_module(module_id: u32, node_id: NodeId) -> Self {
        Self::Module { module_id, node_id }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumString, EnumIter)]
#[strum(serialize_all = "snake_case")]
pub enum PrimitiveKind {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Char,
    Bool,
    #[strum(serialize = "str")]
    String,
    #[strum(serialize = "cstr")]
    CString,
    #[strum(serialize = "bytes")]
    ByteString,
}
