use crate::ast::{Ast, Spanned};
use crate::error::{CompileError, CompilerErrors};
use crate::lexer::lex;
use crate::parsers::parse_toplevel;
use chumsky::{Parser, prelude::*};

pub fn parse<'src>(src: &'src str) -> Result<Ast<'src>, CompilerErrors<'src>> {
    let (tokens, lex_errors) = lex().parse(src).into_output_errors();

    let mut all_errors: Vec<CompileError> =
        lex_errors.into_iter().map(CompileError::from).collect();

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
        all_errors.extend(parse_errors.into_iter().map(CompileError::from));

        // If we have no errors at all, return the parsed result
        if all_errors.is_empty()
            && let Some(parsed) = result
        {
            return Ok(Ast { top_level: parsed });
        }
    }

    // Return all errors we collected
    Err(CompilerErrors::new(src, all_errors))
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

    fn tokens<'src>(src: &'src str) -> Vec<Token<'src>> {
        lex()
            .parse(src)
            .unwrap()
            .into_iter()
            .map(|Spanned(t, _)| t)
            .collect()
    }

    #[test]
    fn test_parse_type() {
        use Type::*;
        let expected = spanned(Function(
            Box::new(spanned(Named("Uuid"))),
            Box::new(spanned(Function(
                Box::new(spanned(Named("Int"))),
                Box::new(spanned(Named("String"))),
            ))),
        ));

        let src = "Uuid -> Int -> String";
        let tokens = lex().parse(src).unwrap();

        let res = crate::parsers::parse_type()
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
        let src = r#"
            pub get_messages;
            get_messages :: Uuid -> Int -> String;
            get_messages user_id page = "hello" |> process 42;
            // comment
            bar |> baz
        "#;

        let expected = vec![
            Token::Public,
            Token::Ident("get_messages"),
            Token::Semicolon,
            Token::Ident("get_messages"),
            Token::DoubleColon,
            Token::Ident("Uuid"),
            Token::Arrow,
            Token::Ident("Int"),
            Token::Arrow,
            Token::Ident("String"),
            Token::Semicolon,
            Token::Ident("get_messages"),
            Token::Ident("user_id"),
            Token::Ident("page"),
            Token::Equals,
            Token::String("hello"),
            Token::Pipe,
            Token::Ident("process"),
            Token::Number(42),
            Token::Semicolon,
            Token::Ident("bar"),
            Token::Pipe,
            Token::Ident("baz"),
        ];

        assert_eq!(tokens(src), expected);
    }

    #[test]
    fn empty_input() {
        assert_eq!(tokens(""), Vec::<Token>::new());
    }

    #[test]
    fn module_export() {
        let src = "pub get_messages, another_function;";

        let expected = vec![spanned(TopLevel::ModuleExport(ModuleExport {
            names: vec!["get_messages", "another_function"],
        }))];

        let tokens = lex().parse(src).unwrap();
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
        let src = "get_messages :: Uuid -> Int -> String;";

        let expected = vec![spanned(TopLevel::TypeAnnotation(TypeAnnotation {
            name: "get_messages",
            ty: Box::new(spanned(Type::Function(
                Box::new(spanned(Type::Named("Uuid"))),
                Box::new(spanned(Type::Function(
                    Box::new(spanned(Type::Named("Int"))),
                    Box::new(spanned(Type::Named("String"))),
                ))),
            ))),
        }))];

        let tokens = lex().parse(src).unwrap();
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
        let src = "get_messages user_id page = user_id page |> process;";

        let expected_function = Function {
            name: "get_messages",
            params: vec!["user_id", "page"],
            expr: Box::new(spanned(Expr::Infix {
                op: crate::ast::InfixOp::Pipe,
                left: Box::new(spanned(Expr::Application(
                    Box::new(spanned(Expr::Ident("user_id"))),
                    Box::new(spanned(Expr::Ident("page"))),
                ))),
                right: Box::new(spanned(Expr::Ident("process"))),
            })),
        };

        let expected = vec![spanned(TopLevel::Function(expected_function))];

        let tokens = lex().parse(src).unwrap();
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
        let src = r#"
            pub get_messages;
            
            get_messages :: Uuid -> Int -> String;
            get_messages user_id page = messages
                |> filter (fn x = x.id + user_id)
                |> process page;
        "#;

        // This should parse without errors
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 3); // export, type annotation, function
    }

    #[test]
    fn arithmetic_expressions() {
        let src = "calc x y = x + y * 2 - 1;";

        let tokens = lex().parse(src).unwrap();
        let result = parse_toplevel()
            .parse(
                tokens
                    .as_slice()
                    .map((src.len()..src.len()).into(), |Spanned(t, s)| (t, s)),
            )
            .unwrap();

        // Should parse as: x + (y * 2) - 1 due to operator precedence
        assert_eq!(result.len(), 1);

        if let TopLevel::Function(func) = &result[0].0 {
            assert_eq!(func.name, "calc");
            assert_eq!(func.params, vec!["x", "y"]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_syntax_file() {
        let src = r#"
            // Module exports
            pub get_messages, process_data, calculate_stats;

            // Type annotations
            get_messages :: Uuid -> Int -> String;
            process_data :: String -> Int -> Bool;
            calculate_stats :: Int -> Int -> Int;

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

        let result = parse(src);
        println!("Parse result: {result:?}");

        // This should parse without errors
        assert!(result.is_ok());

        let parsed = result.unwrap();
        // Should have: 1 export (with 3 names), 3 type annotations, 9 functions = 13 total
        assert_eq!(parsed.top_level.len(), 13);
    }

    #[test]
    fn test_module_exports() {
        let src = "pub func1, func2, func3;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::ModuleExport(export) = &parsed.top_level[0].0 {
            assert_eq!(export.names, vec!["func1", "func2", "func3"]);
        } else {
            panic!("Expected module export");
        }
    }

    #[test]
    fn test_type_annotations() {
        let src = "my_func :: Int -> String -> Bool;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::TypeAnnotation(ann) = &parsed.top_level[0].0 {
            assert_eq!(ann.name, "my_func");
        } else {
            panic!("Expected type annotation");
        }
    }

    #[test]
    fn test_arithmetic_operators() {
        let src = "calc x y = x + y * 2 - 1 / 3;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "calc");
            assert_eq!(func.params, vec!["x", "y"]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_logic_operators() {
        let src = "logic_test a b = a == b && a != 0 || !b;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "logic_test");
            assert_eq!(func.params, vec!["a", "b"]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_field_access() {
        let src = "field_test obj = obj.field.subfield;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "field_test");
            assert_eq!(func.params, vec!["obj"]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_function_application() {
        let src = "apply_test x = f x g y;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "apply_test");
            assert_eq!(func.params, vec!["x"]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_pipe_operator() {
        let src = "pipe_test x = x |> f |> g |> h;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "pipe_test");
            assert_eq!(func.params, vec!["x"]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_lambda_functions() {
        let src = "lambda_test = fn x y = x + y;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "lambda_test");
            assert_eq!(func.params, vec![] as Vec<&str>);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_parenthesized_expressions() {
        let src = "paren_test x = (x + 1) * 2;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "paren_test");
            assert_eq!(func.params, vec!["x"]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_string_literals() {
        let src = r#"string_test = "hello world";"#;
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "string_test");
            assert_eq!(func.params, vec![] as Vec<&str>);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_number_literals() {
        let src = "number_test = 42;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "number_test");
            assert_eq!(func.params, vec![] as Vec<&str>);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_comments() {
        let src = r#"
            // This is a comment
            commented_func = 123; // inline comment
        "#;
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "commented_func");
            assert_eq!(func.params, vec![] as Vec<&str>);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_complex_nested_expressions() {
        let src = "complex a b c = (a + b) * c / 2 == 42 && a.field > 0 || !(b < 0);";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "complex");
            assert_eq!(func.params, vec!["a", "b", "c"]);
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn test_comparison_operators() {
        let src = "compare a b = a < b && a <= b || a > b && a >= b;";
        let result = parse(src);
        assert!(result.is_ok());

        let parsed = result.unwrap();
        assert_eq!(parsed.top_level.len(), 1);

        if let TopLevel::Function(func) = &parsed.top_level[0].0 {
            assert_eq!(func.name, "compare");
            assert_eq!(func.params, vec!["a", "b"]);
        } else {
            panic!("Expected function");
        }
    }
}
