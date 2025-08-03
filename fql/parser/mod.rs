use crate::ast::{Ast, Spanned};
use crate::ctx::CompileContext;
use crate::error::CompileError;
use crate::lexer::lex;
use chumsky::{Parser, prelude::*};
use parsers::parse_toplevel;

pub mod parsers;

pub fn parse(ctx: &CompileContext, src: &str) -> Ast {
    let (tokens, lex_errors) = lex(ctx).parse(src).into_output_errors();

    ctx.extend_errors(lex_errors.into_iter().map(CompileError::from));

    // If we have tokens (even with some lex errors), try to parse them
    if let Some(tokens) = tokens {
        let (result, parse_errors) = parse_toplevel()
            .parse(
                tokens
                    .as_slice()
                    .map((src.len()..src.len()).into(), |Spanned(t, s)| (t, s)),
            )
            .into_output_errors();

        // Add parsing errors to our collection
        ctx.extend_errors(parse_errors.into_iter().map(CompileError::from));

        Ast {
            top_level: result.unwrap_or_default(),
        }
    } else {
        Ast {
            top_level: Vec::new(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::TopLevel;
    use crate::ast::{Expr, Function, ModuleExport, Span, Token, Type, TypeAnnotation};

    fn empty_span() -> Span {
        Span::new((), 0..0)
    }

    fn spanned<T: Clone + PartialEq>(value: T) -> Spanned<T> {
        Spanned(value, empty_span())
    }

    fn tokens(ctx: &CompileContext, src: &str) -> Vec<Token> {
        lex(ctx)
            .parse(src)
            .unwrap()
            .into_iter()
            .map(|Spanned(t, _)| t)
            .collect()
    }

    #[test]
    fn test_parse_type() {
        use Type::*;

        let ctx = CompileContext::default();

        let expected = spanned(Function(
            Box::new(spanned(Application(
                spanned(ctx.intern_static("Uuid")),
                Vec::new(),
            ))),
            Box::new(spanned(Function(
                Box::new(spanned(Application(
                    spanned(ctx.intern_static("Int")),
                    Vec::new(),
                ))),
                Box::new(spanned(Application(
                    spanned(ctx.intern_static("String")),
                    Vec::new(),
                ))),
            ))),
        ));

        let src = "Uuid -> Int -> String";
        let tokens = lex(&ctx).parse(src).unwrap();

        let res = crate::parser::parsers::parse_type()
            .parse(
                tokens
                    .as_slice()
                    .map((src.len()..src.len()).into(), |Spanned(t, s)| (t, s)),
            )
            .unwrap();

        assert_eq!(expected, res);
    }

    #[test]
    fn basic_lexing() {
        let ctx = CompileContext::default();
        let src = r#"
            pub get_messages;
            get_messages: Uuid -> Int -> String;
            get_messages user_id page = "hello" |> process 42;
            // comment
            bar |> baz
        "#;

        let expected = vec![
            Token::Public,
            Token::Ident(ctx.intern_static("get_messages")),
            Token::Semicolon,
            Token::Ident(ctx.intern_static("get_messages")),
            Token::Colon,
            Token::Ident(ctx.intern_static("Uuid")),
            Token::Arrow,
            Token::Ident(ctx.intern_static("Int")),
            Token::Arrow,
            Token::Ident(ctx.intern_static("String")),
            Token::Semicolon,
            Token::Ident(ctx.intern_static("get_messages")),
            Token::Ident(ctx.intern_static("user_id")),
            Token::Ident(ctx.intern_static("page")),
            Token::Equals,
            Token::String(ctx.intern_static("hello")),
            Token::Pipe,
            Token::Ident(ctx.intern_static("process")),
            Token::Number(42),
            Token::Semicolon,
            Token::Ident(ctx.intern_static("bar")),
            Token::Pipe,
            Token::Ident(ctx.intern_static("baz")),
        ];

        assert_eq!(tokens(&ctx, src), expected);
    }

    #[test]
    fn empty_input() {
        assert_eq!(tokens(&CompileContext::default(), ""), Vec::<Token>::new());
    }

    #[test]
    fn module_export() {
        let ctx = CompileContext::default();
        let src = "pub get_messages, another_function;";

        let expected = vec![spanned(TopLevel::ModuleExport(ModuleExport {
            names: vec![
                ctx.intern_static("get_messages"),
                ctx.intern_static("another_function"),
            ],
        }))];

        let tokens = lex(&ctx).parse(src).unwrap();
        let result = parse_toplevel()
            .parse(
                tokens
                    .as_slice()
                    .map((src.len()..src.len()).into(), |Spanned(t, s)| (t, s)),
            )
            .unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn type_annotation() {
        let ctx = CompileContext::default();
        let src = "get_messages: Uuid -> Int -> String;";

        let expected = vec![spanned(TopLevel::TypeAnnotation(TypeAnnotation {
            name: ctx.intern_static("get_messages"),
            ty: spanned(Type::Function(
                Box::new(spanned(Type::Application(
                    spanned(ctx.intern_static("Uuid")),
                    Vec::new(),
                ))),
                Box::new(spanned(Type::Function(
                    Box::new(spanned(Type::Application(
                        spanned(ctx.intern_static("Int")),
                        Vec::new(),
                    ))),
                    Box::new(spanned(Type::Application(
                        spanned(ctx.intern_static("String")),
                        Vec::new(),
                    ))),
                ))),
            )),
        }))];

        let tokens = lex(&ctx).parse(src).unwrap();
        let result = parse_toplevel()
            .parse(
                tokens
                    .as_slice()
                    .map((src.len()..src.len()).into(), |Spanned(t, s)| (t, s)),
            )
            .unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn function_definition() {
        let ctx = CompileContext::default();
        let src = "get_messages user_id page = user_id page |> process;";

        let expected_function = Function {
            name: ctx.intern_static("get_messages"),
            params: vec![ctx.intern_static("user_id"), ctx.intern_static("page")],
            expr: Box::new(spanned(Expr::Infix {
                op: crate::ast::InfixOp::Pipe,
                left: Box::new(spanned(Expr::Application(
                    Box::new(spanned(Expr::Ident(ctx.intern_static("user_id")))),
                    Box::new(spanned(Expr::Ident(ctx.intern_static("page")))),
                ))),
                right: Box::new(spanned(Expr::Ident(ctx.intern_static("process")))),
            })),
        };

        let expected = vec![spanned(TopLevel::Function(expected_function))];

        let tokens = lex(&ctx).parse(src).unwrap();
        let result = parse_toplevel()
            .parse(
                tokens
                    .as_slice()
                    .map((src.len()..src.len()).into(), |Spanned(t, s)| (t, s)),
            )
            .unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn complete_example() {
        let ctx = CompileContext::default();
        let src = r#"
            pub get_messages;

            get_messages: Uuid -> Int -> String;
            get_messages user_id page = messages
                |> filter (fn x = x.id + user_id)
                |> process page;
        "#;

        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 3);
    }

    #[test]
    fn arithmetic_expressions() {
        let ctx = CompileContext::default();
        let src = "calc x y = x + y * 2 - 1;";

        let tokens = lex(&ctx).parse(src).unwrap();
        let result = parse_toplevel()
            .parse(
                tokens
                    .as_slice()
                    .map((src.len()..src.len()).into(), |Spanned(t, s)| (t, s)),
            )
            .unwrap();

        // x + (y * 2) - 1 due to precedence
        assert_eq!(result.len(), 1);
        if let TopLevel::Function(func) = &result[0].0 {
            assert_eq!(func.name, ctx.intern_static("calc"));
            assert_eq!(
                func.params,
                vec![ctx.intern_static("x"), ctx.intern_static("y")]
            );
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_syntax_file() {
        let ctx = CompileContext::default();
        let src = r#"
            // Module exports
            pub get_messages, process_data, calculate_stats;

            // Type annotations
            get_messages: Uuid -> Int -> String;
            process_data: String -> Int -> Bool;
            calculate_stats: Int -> Int -> Int;

            // Basic function with arithmetic
            calculate_stats x y = x + y * 2 - 1;

            // Function with field access
            get_messages user_id page = messages
                |> filter (fn x = x.id == user_id)
                |> skip PAGE_SIZE * page
                |> take PAGE_SIZE
                |> map (fn x = x.content);

            // Logic operators
            process_data input threshold =
                input != "" && input.len > threshold || !is_empty input;

            // Complex nested expressions
            complex_calc a b c =
                (a + b) * c / 2 == 42 &&
                a.field.subfield > 0 ||
                !(b < 0);

            // Function application
            apply_func x = process x |> transform |> validate;

            // Lambda with multiple parameters
            lambda_test = fn x y = x + y * 2;

            // String and number literals
            string_test = "hello world";
            number_test = 42;

            // Comments work too
            // This is a comment
            commented_func = 123; // inline comment
        "#;

        let result = parse(&ctx, src);
        println!("Parse result: {result:#?}");
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 13);
    }

    #[test]
    fn test_module_exports() {
        let ctx = CompileContext::default();
        let src = "pub func1, func2, func3;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::ModuleExport(export) = &result.top_level[0].0 {
            let expected = vec![
                ctx.intern_static("func1"),
                ctx.intern_static("func2"),
                ctx.intern_static("func3"),
            ];
            assert_eq!(export.names, expected);
        } else {
            panic!("Expected module export");
        }
    }

    #[test]
    fn test_type_annotations() {
        let ctx = CompileContext::default();
        let src = "my_func: Int -> String -> Bool;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::TypeAnnotation(ann) = &result.top_level[0].0 {
            assert_eq!(ann.name, ctx.intern_static("my_func"));
        } else {
            panic!("Expected type annotation");
        }
    }

    #[test]
    fn test_arithmetic_operators() {
        let ctx = CompileContext::default();
        let src = "calc x y = x + y * 2 - 1 / 3;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("calc"));
            assert_eq!(
                func.params,
                vec![ctx.intern_static("x"), ctx.intern_static("y")]
            );
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_logic_operators() {
        let ctx = CompileContext::default();
        let src = "logic_test a b = a == b && a != 0 || !b;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("logic_test"));
            assert_eq!(
                func.params,
                vec![ctx.intern_static("a"), ctx.intern_static("b")]
            );
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_field_access() {
        let ctx = CompileContext::default();
        let src = "field_test obj = obj.field.subfield;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("field_test"));
            assert_eq!(func.params, vec![ctx.intern_static("obj")]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_function_application() {
        let ctx = CompileContext::default();
        let src = "apply_test x = f x g y;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("apply_test"));
            assert_eq!(func.params, vec![ctx.intern_static("x")]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_pipe_operator() {
        let ctx = CompileContext::default();
        let src = "pipe_test x = x |> f |> g |> h;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("pipe_test"));
            assert_eq!(func.params, vec![ctx.intern_static("x")]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_lambda_functions() {
        let ctx = CompileContext::default();
        let src = "lambda_test = fn x y = x + y;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("lambda_test"));
            assert!(func.params.is_empty());
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_parenthesized_expressions() {
        let ctx = CompileContext::default();
        let src = "paren_test x = (x + 1) * 2;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("paren_test"));
            assert_eq!(func.params, vec![ctx.intern_static("x")]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_string_literals() {
        let ctx = CompileContext::default();
        let src = r#"string_test = "hello world";"#;
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("string_test"));
            assert!(func.params.is_empty());
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_number_literals() {
        let ctx = CompileContext::default();
        let src = "number_test = 42;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("number_test"));
            assert!(func.params.is_empty());
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_comments() {
        let ctx = CompileContext::default();
        let src = r#"
            // This is a comment
            commented_func = 123; // inline comment
        "#;
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("commented_func"));
            assert!(func.params.is_empty());
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_complex_nested_expressions() {
        let ctx = CompileContext::default();
        let src = "complex a b c = (a + b) * c / 2 == 42 && a.field > 0 || !(b < 0);";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("complex"));
            assert_eq!(
                func.params,
                vec![
                    ctx.intern_static("a"),
                    ctx.intern_static("b"),
                    ctx.intern_static("c"),
                ]
            );
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_comparison_operators() {
        let ctx = CompileContext::default();
        let src = "compare a b = a < b && a <= b || a > b && a >= b;";
        let result = parse(&ctx, src);
        assert!(ctx.errors.borrow().is_empty());
        assert_eq!(result.top_level.len(), 1);

        if let TopLevel::Function(func) = &result.top_level[0].0 {
            assert_eq!(func.name, ctx.intern_static("compare"));
            assert_eq!(
                func.params,
                vec![ctx.intern_static("a"), ctx.intern_static("b")]
            );
        } else {
            panic!("Expected function");
        }
    }
}
