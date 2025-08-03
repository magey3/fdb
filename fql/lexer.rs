use chumsky::prelude::*;

use crate::{
    ast::{Span, Spanned, Token},
    ctx::CompileContext,
};

pub fn lex<'src>(
    ctx: &CompileContext,
) -> impl Parser<'src, &'src str, Vec<Spanned<Token>>, extra::Err<Rich<'src, char, Span>>> {
    let number = text::int(10)
        .to_slice()
        .from_str()
        .unwrapped()
        .map(Token::Number);

    let string = just('"')
        .ignore_then(none_of('"').repeated().to_slice())
        .then_ignore(just('"'))
        .map(|x| Token::String(ctx.intern(x)));

    let ident = text::ascii::ident().map(|x| match x {
        "pub" => Token::Public,
        "fn" => Token::Fn,
        "let" => Token::Let,
        "in" => Token::In,
        "type" => Token::Type,
        s => Token::Ident(ctx.intern(s)),
    });

    let types = choice((just("->").to(Token::Arrow), just(':').to(Token::Colon)));

    let control_flow = choice((just("|>").to(Token::Pipe),));

    let logic = choice((
        just("==").to(Token::Equality),
        just("!=").to(Token::NotEquality),
        just("<=").to(Token::LessThanOrEqual),
        just(">=").to(Token::GreaterThanOrEqual),
        just('<').to(Token::LessThan),
        just('>').to(Token::GreaterThan),
        just("&&").to(Token::And),
        just("||").to(Token::Or),
        just('!').to(Token::Not),
    ));

    let arithmetic = choice((
        just('+').to(Token::Addition),
        just('-').to(Token::Subtraction),
        just('*').to(Token::Multiplication),
        just('/').to(Token::Division),
    ));

    let misc = choice((
        just('=').to(Token::Equals),
        just('.').to(Token::Period),
        just(',').to(Token::Comma),
        just(';').to(Token::Semicolon),
        just('(').to(Token::LeftParen),
        just(')').to(Token::RightParen),
        just('{').to(Token::LeftCurlyBrace),
        just('}').to(Token::RightCurlyBrace),
    ));

    let symbols = choice((types, control_flow, logic, arithmetic, misc));

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
