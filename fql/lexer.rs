use chumsky::prelude::*;

use crate::ast::{Span, Spanned, Token};

pub fn lex<'src>()
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
        // keywords
        just("pub").to(Token::Public),
        just("fn").to(Token::Fn),
        // types
        just("->").to(Token::Arrow),
        just("::").to(Token::DoubleColon),
        // control flow
        just("|>").to(Token::Pipe),
        // logic
        just("==").to(Token::Equality),
        just("!=").to(Token::NotEquality),
        just("<=").to(Token::LessThanOrEqual),
        just(">=").to(Token::GreaterThanOrEqual),
        just('<').to(Token::LessThan),
        just('>').to(Token::GreaterThan),
        just("&&").to(Token::And),
        just("||").to(Token::Or),
        just('!').to(Token::Not),
        // arithmetic
        just('+').to(Token::Addition),
        just('-').to(Token::Subtraction),
        just('*').to(Token::Multiplication),
        just('/').to(Token::Division),
        // misc
        just('=').to(Token::Equals),
        just('.').to(Token::Period),
        just(',').to(Token::Comma),
        just(';').to(Token::Semicolon),
        just(':').to(Token::Colon),
        just('(').to(Token::LeftParen),
        just(')').to(Token::RightParen),
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
