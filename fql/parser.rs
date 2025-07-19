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
pub enum Type {
    Int,
    String,
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeAnnotated<'src> {
    ident: &'src str,
    ty: &'src str,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Query<'src> {
    visibility: Visibility,
    name: &'src str,
    params: Vec<TypeAnnotated<'src>>,
    expr: Box<Expr<'src>>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TopLevel<'src> {
    Query(Query<'src>),
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

    Multiplication,
    Division,
    Addition,
    Subtraction,

    Public,
    Query,
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
        just("query").to(Token::Query),
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
        .map_with(|expr, e| Spanned(expr, e.span()))
        .or(expr
            .clone()
            .delimited_by(just(Token::LeftParen), just(Token::RightParen)));

        atom.pratt((
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
            infix(left(3), just(Token::Addition), |lhs, _, rhs, e| {
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

fn parse_toplevel<'tokens, 'src: 'tokens, I>()
-> impl Parser<'tokens, I, Vec<Spanned<TopLevel<'src>>>, extra::Err<Rich<'tokens, Token<'src>, Span>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    let ident = select! { Token::Ident(ident) => ident }.labelled("identifier");

    let type_annotated = ident
        .then_ignore(just(Token::Colon))
        .then(ident)
        .map(|(ident, ty)| TypeAnnotated { ident, ty });

    let query = just(Token::Public)
        .or_not()
        .then_ignore(just(Token::Query))
        .then(ident)
        .then(
            type_annotated
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .collect()
                .delimited_by(just(Token::LeftParen), just(Token::RightParen)),
        )
        .then_ignore(just(Token::Equals))
        .then(parse_expr())
        .then_ignore(just(Token::Semicolon))
        .map(|(((is_pub, ident), types), Spanned(expr, span))| {
            Spanned(
                Query {
                    visibility: match is_pub {
                        Some(_) => Visibility::Public,
                        None => Visibility::Private,
                    },
                    name: ident,
                    params: types,
                    expr: Box::new(expr),
                },
                span,
            )
        });

    query
        .map_with(|q, span| Spanned(TopLevel::Query(q.0), span.span()))
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
        if all_errors.is_empty() {
            if let Some(parsed) = result {
                return Ok(parsed.into_iter().map(|spanned| spanned.0).collect());
            }
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
    fn basic_lexing() {
        let src = r#"
            pub query foo(a : Int, b: String) = "hello", 42;
            // comment
            bar |> baz
        "#;

        let expected = vec![
            Token::Public,
            Token::Query,
            Token::Ident("foo"),
            Token::LeftParen,
            Token::Ident("a"),
            Token::Colon,
            Token::Ident("Int"),
            Token::Comma,
            Token::Ident("b"),
            Token::Colon,
            Token::Ident("String"),
            Token::RightParen,
            Token::Equals,
            Token::String("hello"),
            Token::Comma,
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
    fn toplevel() {
        let src = r#"
            pub query foo(a: Int, b: String) = a b |> b;
        "#;

        let expected_query = Query {
            visibility: Visibility::Public,
            name: "foo",
            params: vec![
                TypeAnnotated {
                    ident: "a",
                    ty: "Int",
                },
                TypeAnnotated {
                    ident: "b",
                    ty: "String",
                },
            ],
            expr: Box::new(Expr::Pipe(
                Box::new(spanned(Expr::Application(
                    Box::new(spanned(Expr::Ident("a"))),
                    Box::new(spanned(Expr::Ident("b"))),
                ))),
                Box::new(spanned(Expr::Ident("b"))),
            )),
        };

        let expected = vec![Spanned(TopLevel::Query(expected_query), empty_span())];

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
}
