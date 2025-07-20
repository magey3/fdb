use chumsky::{
    input::ValueInput,
    pratt::{infix, left, prefix},
    prelude::*,
};

use crate::ast::{
    Expr, Function, ModuleExport, Span, Spanned, Token, TopLevel, Type, TypeAnnotation,
};

pub fn parse_expr<'tokens, 'src: 'tokens, I>()
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
            // function application and field access
            infix(left(9), just(Token::Period), |lhs, _, rhs, e| {
                Spanned(Expr::FieldAccess(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(8), empty(), |lhs, _, rhs, e| {
                Spanned(Expr::Application(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            // unary
            prefix(7, just(Token::Not), |_, a, e| {
                Spanned(Expr::Not(Box::new(a)), e.span())
            }),
            // arithmetic
            infix(left(6), just(Token::Multiplication), |lhs, _, rhs, e| {
                Spanned(Expr::Multiplication(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(6), just(Token::Division), |lhs, _, rhs, e| {
                Spanned(Expr::Division(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(5), just(Token::Subtraction), |lhs, _, rhs, e| {
                Spanned(Expr::Subtraction(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(5), just(Token::Addition), |lhs, _, rhs, e| {
                Spanned(Expr::Addition(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            // logic
            infix(left(4), just(Token::Equality), |lhs, _, rhs, e| {
                Spanned(Expr::Equality(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(4), just(Token::NotEquality), |lhs, _, rhs, e| {
                Spanned(Expr::NotEquality(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(4), just(Token::LessThan), |lhs, _, rhs, e| {
                Spanned(Expr::LessThan(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(4), just(Token::GreaterThan), |lhs, _, rhs, e| {
                Spanned(Expr::GreaterThan(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(4), just(Token::LessThanOrEqual), |lhs, _, rhs, e| {
                Spanned(
                    Expr::LessThanOrEqual(Box::new(lhs), Box::new(rhs)),
                    e.span(),
                )
            }),
            infix(
                left(4),
                just(Token::GreaterThanOrEqual),
                |lhs, _, rhs, e| {
                    Spanned(
                        Expr::GreaterThanOrEqual(Box::new(lhs), Box::new(rhs)),
                        e.span(),
                    )
                },
            ),
            infix(left(3), just(Token::And), |lhs, _, rhs, e| {
                Spanned(Expr::And(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            infix(left(2), just(Token::Or), |lhs, _, rhs, e| {
                Spanned(Expr::Or(Box::new(lhs), Box::new(rhs)), e.span())
            }),
            // other
            infix(left(1), just(Token::Pipe), |lhs, _, rhs, e| {
                Spanned(Expr::Pipe(Box::new(lhs), Box::new(rhs)), e.span())
            }),
        ))
    })
}

pub fn parse_type<'tokens, 'src: 'tokens, I>()
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

pub fn parse_toplevel<'tokens, 'src: 'tokens, I>()
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
