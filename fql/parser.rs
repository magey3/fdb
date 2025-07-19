use std::ops::{Deref, DerefMut};

use chumsky::{
    input::ValueInput,
    pratt::{infix, left},
    prelude::*,
};

use crate::error::{CompileError, CompilerErrors};

#[derive(Clone, Debug, PartialEq)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'src> {
    // atom
    String(&'src str),
    Ident(&'src str),
    Number(u32),

    // binary operators
    Addition(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Subtraction(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Multiplication(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Division(Box<Spanned<Self>>, Box<Spanned<Self>>),
    FieldAccess(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Pipe(Box<Spanned<Self>>, Box<Spanned<Self>>),
    Application(Box<Spanned<Self>>, Box<Spanned<Self>>),

    Lambda(Vec<Spanned<&'src str>>, Box<Spanned<Self>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeAnnotated<'src> {
    ident: &'src str,
    ty: &'src str,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function<'src> {
    name: &'src str,
    params: Vec<&'src str>,
    expr: Box<Spanned<Expr<'src>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type<'src> {
    Named(&'src str),
    Function(Box<Spanned<Self>>, Box<Spanned<Self>>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeAnnotation<'src> {
    name: &'src str,
    ty: Box<Spanned<Type<'src>>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ModuleExport<'src> {
    names: Vec<&'src str>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TopLevel<'src> {
    ModuleExport(ModuleExport<'src>),
    TypeAnnotation(TypeAnnotation<'src>),
    Function(Function<'src>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token<'src> {
    String(&'src str),
    Ident(&'src str),
    Number(u32),

    LeftParen,
    RightParen,
    Period,
    Comma,
    Semicolon,
    Colon,
    Pipe,
    Equals,

    Arrow,
    DoubleColon,

    Multiplication,
    Division,
    Addition,
    Subtraction,

    Public,
    Fn,
}

pub type Span = chumsky::span::SimpleSpan;
#[derive(Clone, Debug)]
pub struct Spanned<T: Clone + PartialEq>(T, Span);

impl<T: Clone + PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<T: Clone + PartialEq> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Clone + PartialEq> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

fn lex<'src>()
-> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char, Span>>> {
    let number = text::int(10)
        .to_slice()
        .from_str()
        .unwrapped()
        .map(Token::Number);

    let string = just('"')
        .ignore_then(none_of('"').repeated().to_slice())
        .then_ignore(just('"'))
        .map(Token::String);

    let ident = text::ascii::ident().map(Token::Ident);

    let symbols = choice((
        just("pub").to(Token::Public),
        just("fn").to(Token::Fn),
        just("->").to(Token::Arrow),
        just("::").to(Token::DoubleColon),
        just("|>").to(Token::Pipe),
        just('=').to(Token::Equals),
        just('.').to(Token::Period),
        just(',').to(Token::Comma),
        just(';').to(Token::Semicolon),
        just(':').to(Token::Colon),
        just('(').to(Token::LeftParen),
        just(')').to(Token::RightParen),
        just('+').to(Token::Addition),
        just('-').to(Token::Subtraction),
        just('*').to(Token::Multiplication),
        just('/').to(Token::Division),
    ));

    let token = choice((number, string, symbols, ident));

    let comment = just("//")
        .then(any().and_is(just('\n').not()).repeated())
        .padded();

    token
        .map_with(|tok, e| Spanned(tok, e.span()))
        .padded_by(comment.repeated())
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

fn parse_expr<'tokens, 'src: 'tokens, I>()
-> impl Parser<'tokens, I, Spanned<Expr<'src>>, extra::Err<Rich<'tokens, Token<'src>, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    recursive(|expr| {
        let atom = select! {
            Token::String(s) => Expr::String(s),
            Token::Ident(i) => Expr::Ident(i),
            Token::Number(n) => Expr::Number(n),
        }
        .map_with(|expr, e| Spanned(expr, e.span()));

        let parenthesised = expr
            .clone()
            .delimited_by(just(Token::LeftParen), just(Token::RightParen));

        let ident = select! { Token::Ident(i) => i }.map_with(|i, e| Spanned(i, e.span()));

        let lambda = just(Token::Fn)
            .ignore_then(ident.repeated().collect::<Vec<_>>())
            .then_ignore(just(Token::Equals))
            .then(expr.clone())
            .map_with(|(params, expr), e| Spanned(Expr::Lambda(params, Box::new(expr)), e.span()));

        let atoms = choice((parenthesised, lambda, atom));

        atoms.pratt((
            infix(left(5), just(Token::Multiplication), |lhs, _, rhs, e| {
                Spanned(Expr::Subtraction(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(5), just(Token::Division), |lhs, _, rhs, e| {
                Spanned(Expr::Addition(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(4), just(Token::Subtraction), |lhs, _, rhs, e| {
                Spanned(Expr::Subtraction(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(4), just(Token::Addition), |lhs, _, rhs, e| {
                Spanned(Expr::Addition(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(3), just(Token::Period), |lhs, _, rhs, e| {
                Spanned(Expr::FieldAccess(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(2), empty(), |lhs, _, rhs, e| {
                Spanned(Expr::Application(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(1), just(Token::Pipe), |lhs, _, rhs, e| {
                Spanned(Expr::Pipe(Box::new(lhs), Box::new(rhs)), e.span())
            }),
        ))
    })
}

fn parse_type<'tokens, 'src: 'tokens, I>()
-> impl Parser<'tokens, I, Spanned<Type<'src>>, extra::Err<Rich<'tokens, Token<'src>, Span>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    recursive(|ty| {
        let named = select! { Token::Ident(ident) => Type::Named(ident) }
            .labelled("named type")
            .map_with(|ty, e| Spanned(ty, e.span()));

        let function = named
            .then_ignore(just(Token::Arrow))
            .then(ty)
            .map_with(|(lhs, rhs), e| {
                Spanned(Type::Function(Box::new(lhs), Box::new(rhs)), e.span())
            });

        function.or(named)
    })
}

fn parse_toplevel<'tokens, 'src: 'tokens, I>()
-> impl Parser<'tokens, I, Vec<Spanned<TopLevel<'src>>>, extra::Err<Rich<'tokens, Token<'src>, Span>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    let ident = select! { Token::Ident(ident) => ident }.labelled("identifier");

    let module_export = just(Token::Public)
        .ignore_then(
            ident
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .at_least(1)
                .collect::<Vec<_>>()
                .map(|x| ModuleExport { names: x }),
        )
        .then_ignore(just(Token::Semicolon))
        .map(TopLevel::ModuleExport);

    let type_annotation = ident
        .then_ignore(just(Token::DoubleColon))
        .then(parse_type())
        .then_ignore(just(Token::Semicolon))
        .map(|(name, ty)| {
            TopLevel::TypeAnnotation(TypeAnnotation {
                name,
                ty: Box::new(ty),
            })
        });

    let query = ident
        .then(ident.repeated().collect::<Vec<_>>())
        .then_ignore(just(Token::Equals))
        .then(parse_expr())
        .then_ignore(just(Token::Semicolon))
        .map(|((name, params), expr)| Function {
            name,
            params,
            expr: Box::new(expr),
        })
        .map(TopLevel::Function);

    let top_level = choice((module_export, type_annotation, query));

    top_level
        .map_with(|q, span| Spanned(q, span.span()))
        .repeated()
        .collect()
}

pub fn parse<'src>(src: &'src str) -> Result<Vec<TopLevel<'src>>, CompilerErrors<'src>> {
    let (tokens, lex_errors) = lex().parse(src).into_output_errors();

    let mut all_errors: Vec<CompileError> = lex_errors.into_iter().map(|x| x.into()).collect();

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
        all_errors.extend(parse_errors.into_iter().map(|x| x.into()));

        // If we have no errors at all, return the parsed result
        if all_errors.is_empty()
            && let Some(parsed) = result
        {
            return Ok(parsed.into_iter().map(|spanned| spanned.0).collect());
        }
    }

    // Return all errors we collected
    Err(CompilerErrors::new(src, all_errors))
}

#[cfg(test)]
mod test {
    use super::*;

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

        let res = parse_type()
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
            expr: Box::new(spanned(Expr::Pipe(
                Box::new(spanned(Expr::Application(
                    Box::new(spanned(Expr::Ident("user_id"))),
                    Box::new(spanned(Expr::Ident("page"))),
                ))),
                Box::new(spanned(Expr::Ident("process"))),
            ))),
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
        assert_eq!(parsed.len(), 3); // export, type annotation, function
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
}
