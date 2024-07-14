use crate::{
    ast::{
        AssignmentOperatorKind, BinaryOperator, BinaryOperatorKind, Block, Expression,
        ExpressionKind, FunctionCallArgumentList, FunctionDefinition, FunctionParameter,
        FunctionParameterList, FunctionSignature, Identifier, InternedSymbol, Literal, LiteralKind,
        Local, LocalKind, Module, QualifiedIdentifier, Statement, StatementKind, Type, TypeKind,
        UnaryOperator, UnaryOperatorKind,
    },
    lexer::{Keyword, Lexer, Span, Token, TokenKind},
    SourceFile,
};

#[derive(Debug)]
pub struct Parser<'source> {
    lexer: Lexer<'source>,
}

#[derive(Debug)]
enum ModuleItem {
    FunctionDefinition(FunctionDefinition),
}

impl<'source> Parser<'source> {
    pub fn parse_module(source_file: &'source SourceFile) -> Module {
        let mut parser = Self {
            lexer: Lexer::new(source_file),
        };

        let mut module = Module {
            function_definitions: Vec::new(),
        };

        while !parser.lexer.is_eof() && parser.lexer.peek().is_some() {
            match parser.parse_module_item() {
                ModuleItem::FunctionDefinition(f) => module.function_definitions.push(f),
            }
        }

        module
    }

    fn report_fatal_error(&self, message: &str) -> ! {
        eprintln!(
            "Fatal error reported in Parser ({}:{}:{}):",
            self.lexer.source().path.display(),
            self.lexer.line_number() + 1,
            self.lexer.column()
        );
        eprintln!("{message}");
        std::process::exit(1);
    }

    fn expect_peek(&mut self, expecting: &str) -> Token {
        let Some(token) = self.lexer.peek() else {
            self.report_fatal_error(&format!("Expected {expecting} but reached end of file",))
        };

        token
    }

    fn expect_next(&mut self, expecting: &str) -> Token {
        let Some(token) = self.lexer.next() else {
            self.report_fatal_error(&format!("Expected {expecting} but reached end of file",))
        };

        token
    }

    fn expect_next_to_be(&mut self, kind: TokenKind) -> Token {
        let token = self.expect_next(&format!("{kind:?}"));

        if token.kind != kind {
            self.report_fatal_error(&format!(
                "Expected {:?} but found {:?} ({})",
                kind,
                token.kind,
                self.lexer.source().value_of_span(token.span)
            ))
        }

        token
    }

    fn expect_keyword(&mut self, keyword: Keyword) -> Token {
        self.expect_next_to_be(TokenKind::Keyword(keyword))
    }

    fn parse_module_item(&mut self) -> ModuleItem {
        let Some(peeked) = self.lexer.peek() else {
            self.report_fatal_error("Unexpected EOF while trying to parse module item")
        };

        match peeked.kind {
            TokenKind::Keyword(Keyword::Fn) => {
                ModuleItem::FunctionDefinition(self.parse_function_definition())
            }
            _ => self.report_fatal_error(&format!(
                "Expected function definition in module but found: {} ({:?})",
                self.lexer.source().value_of_span(peeked.span),
                peeked.kind
            )),
        }
    }

    /// fn name(param: ty) -> return_type {}
    fn parse_function_definition(&mut self) -> FunctionDefinition {
        self.expect_keyword(Keyword::Fn);

        let signature = self.parse_function_signature();
        let body = self.parse_block();

        FunctionDefinition { signature, body }
    }

    /// name(param: ty) -> return_type
    fn parse_function_signature(&mut self) -> FunctionSignature {
        let name = self.parse_identifier();
        let parameters = self.parse_function_parameter_list();

        let return_type = (self.expect_peek("arrow or opening brace").kind == TokenKind::Arrow)
            .then(|| {
                self.expect_next_to_be(TokenKind::Arrow);
                self.parse_type()
            });

        let span = Span::new(
            name.span.start,
            return_type
                .as_ref()
                .map(|return_type| return_type.span.end)
                .unwrap_or(parameters.span.end),
        );

        FunctionSignature {
            span,
            name,
            parameters,
            return_type,
        }
    }

    // main
    fn parse_identifier(&mut self) -> Identifier {
        let token = self.expect_next_to_be(TokenKind::Identifier);
        let value = self.lexer.source().value_of_span(token.span);

        Identifier {
            span: token.span,
            symbol: InternedSymbol::new(value),
        }
    }

    // std::fs::read_to_string
    fn parse_qualified_identifier(&mut self) -> QualifiedIdentifier {
        let mut segments = vec![self.parse_identifier()];

        // While the next token is a double colon try and parse more segments
        while self
            .lexer
            .peek()
            .is_some_and(|t| t.kind == TokenKind::DoubleColon)
        {
            self.expect_next_to_be(TokenKind::DoubleColon);
            segments.push(self.parse_identifier());
        }

        QualifiedIdentifier {
            span: Span::new(
                segments.first().unwrap().span.start,
                segments.last().unwrap().span.end,
            ),
            segments,
        }
    }

    // (argc: usize, argv: &[str])
    fn parse_function_parameter_list(&mut self) -> FunctionParameterList {
        let mut parameters = Vec::new();

        let open_paren = self.expect_next_to_be(TokenKind::OpenParen);

        // If the next token is not a closing paren, try parsing function
        // parameters
        if self.expect_peek("function parameter or closing paren").kind != TokenKind::CloseParen {
            // If a close paren was not found then there MUST be at least one
            // parameter
            parameters.push(self.parse_function_parameter());

            // While the next token is a comma try and parse more parameters
            while self
                .lexer
                .peek()
                .is_some_and(|t| t.kind == TokenKind::Comma)
            {
                self.expect_next_to_be(TokenKind::Comma);
                parameters.push(self.parse_function_parameter());
            }
        }

        let close_paren = self.expect_next_to_be(TokenKind::CloseParen);

        FunctionParameterList {
            span: Span::new(open_paren.span.start, close_paren.span.end),
            parameters,
        }
    }

    // argc: usize
    fn parse_function_parameter(&mut self) -> FunctionParameter {
        let name = self.parse_identifier();
        self.expect_next_to_be(TokenKind::Colon);
        let ty = self.parse_type();

        FunctionParameter {
            span: Span::new(name.span.start, ty.span.end),
            name,
            ty,
        }
    }

    // i32
    fn parse_type(&mut self) -> Type {
        let identifier = self.parse_qualified_identifier();

        Type {
            span: identifier.span,
            kind: TypeKind::QualifiedIdentifier(identifier),
        }
    }

    // "{" ( statement )* "}"
    fn parse_block(&mut self) -> Block {
        let mut statements = Vec::new();

        let open_brace = self.expect_next_to_be(TokenKind::OpenBrace);

        // If the next token is not a closing brace, try parsing statements
        if self.expect_peek("function parameter or closing paren").kind != TokenKind::CloseBrace {
            // If a close brace was not found then there MUST be at least one
            // statement
            statements.push(self.parse_statement());

            // While the next token is a comma try and parse more parameters
            while !self
                .lexer
                .peek()
                .is_some_and(|t| t.kind == TokenKind::CloseBrace)
            {
                statements.push(self.parse_statement());
            }
        }

        let close_brace = self.expect_next_to_be(TokenKind::CloseBrace);

        Block {
            span: Span::new(open_brace.span.start, close_brace.span.end),
            statements,
        }
    }

    fn parse_statement(&mut self) -> Statement {
        if self.expect_peek("let keyword or expression").kind == TokenKind::Keyword(Keyword::Let) {
            let local = self.parse_local();

            return Statement {
                span: local.span,
                kind: StatementKind::Local(Box::new(local)),
            };
        }

        if self.expect_peek("expression").kind == TokenKind::Semicolon {
            let semicolon = self.expect_next_to_be(TokenKind::Semicolon);

            return Statement {
                span: semicolon.span,
                kind: StatementKind::Empty,
            };
        }

        let expression = self.parse_expression();

        // TODO: require a semicolon unless reached end of block or we just parsed an expression with a block

        let peeked = self.expect_peek("semicolon or closing brace");

        // If the next token is not a semicolon, we need to perform some extra
        // checks: it has to be a closing brace (reached end of block) or we
        // need to have just parsed an expression with a block
        if peeked.kind != TokenKind::Semicolon {
            if peeked.kind != TokenKind::CloseBrace
                && !matches!(
                    expression.kind,
                    ExpressionKind::Block(_)
                        | ExpressionKind::If { .. }
                        | ExpressionKind::While { .. }
                )
            {
                self.report_fatal_error(&format!(
                    "Expected semicolon after statement but found {:?} ({})",
                    peeked.kind,
                    self.lexer.source().value_of_span(peeked.span),
                ))
            }

            return Statement {
                span: expression.span,
                kind: StatementKind::BareExpr(Box::new(expression)),
            };
        }

        let semicolon = self.expect_next_to_be(TokenKind::Semicolon);

        Statement {
            span: Span::new(expression.span.start, semicolon.span.end),
            kind: StatementKind::SemiExpr(Box::new(expression)),
        }
    }

    fn parse_local(&mut self) -> Local {
        let let_keyword = self.expect_keyword(Keyword::Let);

        let is_mutable = if self
            .expect_peek("mut keyword, type qualifier, or assignment operator")
            .kind
            == TokenKind::Keyword(Keyword::Mut)
        {
            self.expect_keyword(Keyword::Mut);
            true
        } else {
            false
        };

        let name = self.parse_identifier();

        let ty = if self.expect_peek("colon, equals, or semicolon").kind == TokenKind::Colon {
            self.expect_next_to_be(TokenKind::Arrow);
            Some(self.parse_type())
        } else {
            None
        };

        let (span, kind) = if self.expect_peek("equals or semicolon").kind == TokenKind::Semicolon {
            let semicolon = self.expect_next_to_be(TokenKind::Semicolon);

            (
                Span::new(let_keyword.span.start, semicolon.span.end),
                LocalKind::Declaration,
            )
        } else {
            self.expect_next_to_be(TokenKind::Equals);

            let expression = self.parse_expression();
            let semicolon = self.expect_next_to_be(TokenKind::Semicolon);

            (
                Span::new(let_keyword.span.start, semicolon.span.end),
                LocalKind::Initialization(Box::new(expression)),
            )
        };

        Local {
            span,
            is_mutable,
            name,
            ty,
            kind,
        }
    }

    /// expression     -> return
    /// return         -> ( "break" | "continue" )
    ///                   | "return" ( assignment )?
    ///                   | assignment
    /// assignment     -> logical_or ( ( "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&&=" | "||=" | "&=" | "|=" | "^=" | "<<=" | ">>=" ) assignment )*
    /// logical_or     -> logical_and ( "||" logical_and )*
    /// logical_and    -> comparison ( "&&" comparison )*
    /// comparison     -> bitwise_or ( ( "!=" | "==" | "<" | "<=" | ">" | ">=" ) bitwise_or )*
    /// bitwise_or     -> bitwise_xor ( "|" bitwise_xor )*
    /// bitwise_xor    -> bitwise_and ( "^" bitwise_and )*
    /// bitwise_and    -> bit_shift ( "&" bit_shift )*
    /// bit_shift      -> term ( ( "<<" | ">>" ) term )*
    /// term           -> factor ( ( "-" | "+" ) factor )*
    /// factor         -> cast ( ( "/" | "*" | "%" ) cast )*
    /// cast           -> unary ( "as" TYPE )*
    /// unary          -> ( "!" | "-" | "*" ) function_call
    ///                   | function_call
    /// function_call  -> block ( "(" ( expression ( "," expression )* )? ")" )*
    /// block          -> BLOCK
    ///                   | "if" expression BLOCK ( "else" expression )?
    ///                   | "while" expression BLOCK
    ///                   | atom
    /// atom           -> IDENTIFIER | NUMBER | STRING | BOOL
    ///                   | "(" expression ")"
    fn parse_expression(&mut self) -> Expression {
        // We start from the top and work our way down.

        if self.expect_peek("expression").kind == TokenKind::Keyword(Keyword::Break) {
            let break_keyword = self.expect_keyword(Keyword::Break);

            return Expression {
                span: break_keyword.span,
                kind: ExpressionKind::Break,
            };
        }

        if self.expect_peek("expression").kind == TokenKind::Keyword(Keyword::Continue) {
            let continue_keyword = self.expect_keyword(Keyword::Continue);

            return Expression {
                span: continue_keyword.span,
                kind: ExpressionKind::Continue,
            };
        }

        if self.expect_peek("expression").kind == TokenKind::Keyword(Keyword::Return) {
            let return_keyword = self.expect_keyword(Keyword::Return);
            let assignment = self.parse_assignment_expression();

            let peeked = self.expect_peek("semicolon, closing brace, or expression");

            // Unless we are at the end of a block or have a semicolon we expect an expression to follow
            let expression = (peeked.kind != TokenKind::Semicolon
                && peeked.kind != TokenKind::CloseBrace)
                .then(|| self.parse_expression());

            return Expression {
                span: Span::new(
                    return_keyword.span.start,
                    expression
                        .as_ref()
                        .map(|e| e.span.end)
                        .unwrap_or(assignment.span.end),
                ),
                kind: ExpressionKind::Return(expression.map(Box::new)),
            };
        }

        self.parse_assignment_expression()
    }

    fn parse_assignment_expression(&mut self) -> Expression {
        let mut expression = self.parse_logical_or_expression();

        while self
            .expect_peek("assignment operator or expression")
            .kind
            .is_assignment_operator()
        {
            let operator = self.parse_assignment_operator();
            let rhs = self.parse_assignment_expression();

            let span = Span::new(expression.span.start, rhs.span.end);

            // We know that the operator was either an "=" or a special
            // assignment operator, but the parse_assignment_operator function
            // returns None in the case of "=" so we can easily branch based on
            // that fact
            expression = if let Some(operator) = operator {
                Expression {
                    span,
                    kind: ExpressionKind::OperatorAssignment {
                        operator,
                        lhs: Box::new(expression),
                        rhs: Box::new(rhs),
                    },
                }
            } else {
                Expression {
                    span,
                    kind: ExpressionKind::Assignment {
                        lhs: Box::new(expression),
                        rhs: Box::new(rhs),
                    },
                }
            }
        }

        expression
    }

    fn parse_assignment_operator(&mut self) -> Option<AssignmentOperatorKind> {
        let operator = self.expect_next("assignment operator");

        Some(match operator.kind {
            TokenKind::PlusEquals => AssignmentOperatorKind::Add,
            TokenKind::MinusEquals => AssignmentOperatorKind::Subtract,
            TokenKind::MultiplyEquals => AssignmentOperatorKind::Multiply,
            TokenKind::DivideEquals => AssignmentOperatorKind::Divide,
            TokenKind::ModulusEquals => AssignmentOperatorKind::Modulus,
            TokenKind::LogicalAndEquals => AssignmentOperatorKind::LogicalAnd,
            TokenKind::LogicalOrEquals => AssignmentOperatorKind::LogicalOr,
            TokenKind::BitwiseXorEquals => AssignmentOperatorKind::BitwiseXor,
            TokenKind::BitwiseAndEquals => AssignmentOperatorKind::BitwiseAnd,
            TokenKind::BitwiseOrEquals => AssignmentOperatorKind::BitwiseOr,
            TokenKind::ShiftLeftEquals => AssignmentOperatorKind::ShiftLeft,
            TokenKind::ShiftRightEquals => AssignmentOperatorKind::ShiftRight,
            _ => return None,
        })
    }

    fn parse_logical_or_expression(&mut self) -> Expression {
        let mut expression = self.parse_logical_and_expression();

        while self.expect_peek("logical or operator or expression").kind == TokenKind::LogicalOr {
            let operator = self.expect_next_to_be(TokenKind::LogicalOr);
            let rhs = self.parse_logical_and_expression();

            expression = Expression {
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator: BinaryOperator {
                        span: operator.span,
                        kind: BinaryOperatorKind::LogicalOr,
                    },
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_logical_and_expression(&mut self) -> Expression {
        let mut expression = self.parse_comparison_expression();

        while self.expect_peek("logical and operator or expression").kind == TokenKind::LogicalAnd {
            let operator = self.expect_next_to_be(TokenKind::LogicalAnd);
            let rhs = self.parse_comparison_expression();

            expression = Expression {
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator: BinaryOperator {
                        span: operator.span,
                        kind: BinaryOperatorKind::LogicalAnd,
                    },
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_comparison_expression(&mut self) -> Expression {
        let mut expression = self.parse_bitwise_or_expression();

        while self
            .expect_peek("comparison operator or expression")
            .kind
            .is_comparison_operator()
        {
            let operator = self.parse_comparison_operator();
            let rhs = self.parse_bitwise_or_expression();

            expression = Expression {
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator,
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_comparison_operator(&mut self) -> BinaryOperator {
        let operator = self.expect_next("comparison operator");

        BinaryOperator {
            span: operator.span,
            kind: match operator.kind {
                TokenKind::NotEquals => BinaryOperatorKind::NotEquals,
                TokenKind::DoubleEquals => BinaryOperatorKind::Equals,
                TokenKind::LessThan => BinaryOperatorKind::LessThan,
                TokenKind::LessThanOrEqualTo => BinaryOperatorKind::LessThanOrEqualTo,
                TokenKind::GreaterThan => BinaryOperatorKind::GreaterThan,
                TokenKind::GreaterThanOrEqualTo => BinaryOperatorKind::GreaterThanOrEqualTo,
                _ => unreachable!(),
            },
        }
    }

    fn parse_bitwise_or_expression(&mut self) -> Expression {
        let mut expression = self.parse_bitwise_xor_expression();

        while self.expect_peek("bitwise or operator or expression").kind == TokenKind::BitwiseOr {
            let operator = self.expect_next_to_be(TokenKind::BitwiseOr);
            let rhs = self.parse_bitwise_xor_expression();

            expression = Expression {
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator: BinaryOperator {
                        span: operator.span,
                        kind: BinaryOperatorKind::BitwiseOr,
                    },
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_bitwise_xor_expression(&mut self) -> Expression {
        let mut expression = self.parse_bitwise_and_expression();

        while self.expect_peek("bitwise xor operator or expression").kind == TokenKind::BitwiseXor {
            let operator = self.expect_next_to_be(TokenKind::BitwiseXor);
            let rhs = self.parse_bitwise_and_expression();

            expression = Expression {
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator: BinaryOperator {
                        span: operator.span,
                        kind: BinaryOperatorKind::BitwiseXor,
                    },
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_bitwise_and_expression(&mut self) -> Expression {
        let mut expression = self.parse_bit_shift_expression();

        while self.expect_peek("bitwise and operator or expression").kind == TokenKind::BitwiseAnd {
            let operator = self.expect_next_to_be(TokenKind::BitwiseAnd);
            let rhs = self.parse_bit_shift_expression();

            expression = Expression {
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator: BinaryOperator {
                        span: operator.span,
                        kind: BinaryOperatorKind::BitwiseAnd,
                    },
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_bit_shift_expression(&mut self) -> Expression {
        let mut expression = self.parse_term_expression();

        while self
            .expect_peek("bit shift operator or expression")
            .kind
            .is_bit_shift_operator()
        {
            let operator = self.parse_bit_shift_operator();
            let rhs = self.parse_term_expression();

            expression = Expression {
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator,
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_bit_shift_operator(&mut self) -> BinaryOperator {
        let operator = self.expect_next("bit shift operator");

        BinaryOperator {
            span: operator.span,
            kind: match operator.kind {
                TokenKind::ShiftLeft => BinaryOperatorKind::ShiftLeft,
                TokenKind::ShiftRight => BinaryOperatorKind::ShiftRight,
                _ => unreachable!(),
            },
        }
    }

    fn parse_term_expression(&mut self) -> Expression {
        let mut expression = self.parse_factor_expression();

        while self
            .expect_peek("term operator or expression")
            .kind
            .is_term_operator()
        {
            let operator = self.parse_term_operator();
            let rhs = self.parse_factor_expression();

            expression = Expression {
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator,
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_term_operator(&mut self) -> BinaryOperator {
        let operator = self.expect_next("term operator");

        BinaryOperator {
            span: operator.span,
            kind: match operator.kind {
                TokenKind::Plus => BinaryOperatorKind::Add,
                TokenKind::Minus => BinaryOperatorKind::Subtract,
                _ => unreachable!(),
            },
        }
    }

    fn parse_factor_expression(&mut self) -> Expression {
        let mut expression = self.parse_cast_expression();

        while self
            .expect_peek("factor operator or expression")
            .kind
            .is_factor_operator()
        {
            let operator = self.parse_factor_operator();
            let rhs = self.parse_cast_expression();

            expression = Expression {
                span: Span::new(expression.span.start, rhs.span.end),
                kind: ExpressionKind::Binary {
                    lhs: Box::new(expression),
                    operator,
                    rhs: Box::new(rhs),
                },
            }
        }

        expression
    }

    fn parse_factor_operator(&mut self) -> BinaryOperator {
        let operator = self.expect_next("factor operator");

        BinaryOperator {
            span: operator.span,
            kind: match operator.kind {
                TokenKind::Asterisk => BinaryOperatorKind::Multiply,
                TokenKind::Divide => BinaryOperatorKind::Divide,
                TokenKind::Modulus => BinaryOperatorKind::Modulus,
                _ => unreachable!(),
            },
        }
    }

    fn parse_cast_expression(&mut self) -> Expression {
        let mut expression = self.parse_unary_expression();

        while self.expect_peek("as keyword or expression").kind == TokenKind::Keyword(Keyword::As) {
            self.expect_keyword(Keyword::As);
            let ty = self.parse_type();

            expression = Expression {
                span: Span::new(expression.span.start, ty.span.end),
                kind: ExpressionKind::Cast {
                    expression: Box::new(expression),
                    ty: Box::new(ty),
                },
            }
        }

        expression
    }

    fn parse_unary_expression(&mut self) -> Expression {
        if self
            .expect_peek("as keyword or expression")
            .kind
            .is_unary_operator()
        {
            let operator = self.parse_unary_operator();
            let operand = self.parse_function_call_expression();

            return Expression {
                span: Span::new(operator.span.start, operand.span.end),
                kind: ExpressionKind::Unary {
                    operator,
                    operand: Box::new(operand),
                },
            };
        }

        self.parse_function_call_expression()
    }

    fn parse_unary_operator(&mut self) -> UnaryOperator {
        let operator = self.expect_next("unary operator");

        UnaryOperator {
            span: operator.span,
            kind: match operator.kind {
                TokenKind::Asterisk => UnaryOperatorKind::Deref,
                TokenKind::Bang => UnaryOperatorKind::Invert,
                TokenKind::Minus => UnaryOperatorKind::Negate,
                _ => unreachable!(),
            },
        }
    }

    fn parse_function_call_expression(&mut self) -> Expression {
        let mut expression = self.parse_expression_with_block();

        while self
            .expect_peek("open parenthesis, semicolon, or closing brace")
            .kind
            == TokenKind::OpenParen
        {
            let arguments = self.parse_function_call_arguments();

            expression = Expression {
                span: Span::new(expression.span.start, arguments.span.end),
                kind: ExpressionKind::FunctionCall {
                    function: Box::new(expression),
                    arguments: Box::new(arguments),
                },
            }
        }

        expression
    }

    fn parse_function_call_arguments(&mut self) -> FunctionCallArgumentList {
        let mut arguments = Vec::new();

        let open_paren = self.expect_next_to_be(TokenKind::OpenParen);

        // If the next token is not a closing paren, try parsing function call
        // arguments
        if self
            .expect_peek("function call argument or closing paren")
            .kind
            != TokenKind::CloseParen
        {
            // If a close paren was not found then there MUST be at least one
            // argument
            arguments.push(self.parse_expression());

            // While the next token is a comma try and parse more parameters
            while self
                .lexer
                .peek()
                .is_some_and(|t| t.kind == TokenKind::Comma)
            {
                self.expect_next_to_be(TokenKind::Comma);
                arguments.push(self.parse_expression());
            }
        }

        let close_paren = self.expect_next_to_be(TokenKind::CloseParen);

        FunctionCallArgumentList {
            span: Span::new(open_paren.span.start, close_paren.span.end),
            arguments,
        }
    }

    fn parse_expression_with_block(&mut self) -> Expression {
        if self
            .expect_peek("opening brace, if expression, while expression, or atomic expression")
            .kind
            == TokenKind::OpenBrace
        {
            return self.parse_block_expression();
        }

        if self
            .expect_peek("if expression, while expression, or atomic expression")
            .kind
            == TokenKind::Keyword(Keyword::If)
        {
            return self.parse_if_expression();
        }

        if self
            .expect_peek("while expression or atomic expression")
            .kind
            == TokenKind::Keyword(Keyword::While)
        {
            return self.parse_while_expression();
        }

        self.parse_atomic_expression()
    }

    fn parse_block_expression(&mut self) -> Expression {
        let block = self.parse_block();

        Expression {
            span: block.span,
            kind: ExpressionKind::Block(Box::new(block)),
        }
    }

    /// "if" expression BLOCK ( "else" expression )?
    fn parse_if_expression(&mut self) -> Expression {
        let if_keyword = self.expect_keyword(Keyword::If);
        let condition = self.parse_expression();
        let positive = self.parse_block();

        let negative = (self
            .expect_peek("else keyword, semicolon, or close brace")
            .kind
            == TokenKind::Keyword(Keyword::Else))
        .then(|| {
            self.expect_keyword(Keyword::Else);

            let peeked = self.expect_peek("if keyword or opening brace");

            if peeked.kind == TokenKind::Keyword(Keyword::If) {
                return self.parse_if_expression();
            }

            if peeked.kind == TokenKind::OpenBrace {
                return self.parse_block_expression();
            }

            self.report_fatal_error(&format!(
                "Expected if expression or block after else keyword but found {:?} ({})",
                peeked.kind,
                self.lexer.source().value_of_span(peeked.span)
            ))
        });

        Expression {
            span: Span::new(
                if_keyword.span.start,
                negative
                    .as_ref()
                    .map(|n: &Expression| n.span.end)
                    .unwrap_or(positive.span.end),
            ),
            kind: ExpressionKind::If {
                condition: Box::new(condition),
                positive: Box::new(positive),
                negative: negative.map(Box::new),
            },
        }
    }

    /// "while" expression BLOCK
    fn parse_while_expression(&mut self) -> Expression {
        let while_keyword = self.expect_keyword(Keyword::While);
        let condition = self.parse_expression();
        let block = self.parse_block();

        Expression {
            span: Span::new(while_keyword.span.start, block.span.end),
            kind: ExpressionKind::While {
                condition: Box::new(condition),
                block: Box::new(block),
            },
        }
    }

    fn parse_atomic_expression(&mut self) -> Expression {
        // Check for qualified identifier
        if self
            .expect_peek("qualified identifier, open paren, or literal expression")
            .kind
            == TokenKind::Identifier
        {
            let qualified_identifier = self.parse_qualified_identifier();

            return Expression {
                span: qualified_identifier.span,
                kind: ExpressionKind::QualifiedIdentifier(Box::new(qualified_identifier)),
            };
        }

        // Check for grouping
        if self.expect_peek("open paren, or literal expression").kind == TokenKind::OpenParen {
            return self.parse_grouping_expression();
        }

        // Assume it's a literal (no other valid options)
        let literal = self.parse_literal();

        Expression {
            span: literal.span,
            kind: ExpressionKind::Literal(Box::new(literal)),
        }
    }

    fn parse_grouping_expression(&mut self) -> Expression {
        let open_paren = self.expect_next_to_be(TokenKind::OpenParen);
        let expression = self.parse_expression();
        let close_paren = self.expect_next_to_be(TokenKind::CloseParen);

        Expression {
            span: Span::new(open_paren.span.start, close_paren.span.end),
            kind: ExpressionKind::Grouping(Box::new(expression)),
        }
    }

    fn parse_literal(&mut self) -> Literal {
        let token = self.expect_next("literal");

        let kind = match token.kind {
            TokenKind::BooleanLiteral => LiteralKind::Boolean,
            TokenKind::ByteLiteral => LiteralKind::Byte,
            TokenKind::CharLiteral => LiteralKind::Char,
            TokenKind::IntegerLiteral => LiteralKind::Integer,
            TokenKind::FloatLiteral => LiteralKind::Float,
            TokenKind::StringLiteral => LiteralKind::String,
            TokenKind::ByteStringLiteral => LiteralKind::ByteString,
            TokenKind::CStringLiteral => LiteralKind::CString,
            k => self.report_fatal_error(&format!(
                "Expected literal but found {:?} ({})",
                k,
                self.lexer.source().value_of_span(token.span)
            )),
        };
        let value = self.lexer.source().value_of_span(token.span);

        Literal {
            span: token.span,
            kind,
            symbol: InternedSymbol::new(value),
        }
    }
}
