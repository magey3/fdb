use chumsky::{error::Rich, span::Span as _};
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::parser::{Span, Token};

#[derive(Error, Diagnostic, Debug)]
#[error("Errors occured during compilation")]
#[diagnostic()]
pub struct CompilerErrors<'src> {
    #[source_code]
    src: &'src str,
    #[related]
    errors: Vec<CompileError>,
}

impl<'src> CompilerErrors<'src> {
    pub fn new(src: &'src str, errors: impl Into<Vec<CompileError>>) -> Self {
        Self {
            src: src.as_ref(),
            errors: errors.into(),
        }
    }
}

#[derive(Error, Diagnostic, Debug)]
pub enum CompileError {
    #[error("Missing semicolon")]
    #[diagnostic(
        code(parser::missing_semicolon),
        help("Add a semicolon at the end of the statement")
    )]
    MissingSemicolon {
        #[label("expected semicolon here")]
        span: SourceSpan,
    },

    #[error("Expected {expected}, found {found}")]
    #[diagnostic(code(parser::unexpected_token))]
    UnexpectedToken {
        expected: String,
        found: String,
        #[label("unexpected token")]
        span: SourceSpan,
    },

    #[error("Invalid syntax")]
    #[diagnostic(code(parser::invalid_syntax))]
    InvalidSyntax {
        #[label("invalid syntax here")]
        span: SourceSpan,
        #[help]
        help: Option<String>,
    },

    #[error("Unterminated string literal")]
    #[diagnostic(
        code(parser::unterminated_string),
        help("Close the string with a quote")
    )]
    UnterminatedString {
        #[label("string starts here")]
        span: SourceSpan,
    },

    #[error("Invalid number format")]
    #[diagnostic(code(parser::invalid_number))]
    InvalidNumber {
        #[label("invalid number")]
        span: SourceSpan,
    },
}

impl<'src> From<Rich<'src, char, Span>> for CompileError {
    fn from(value: Rich<'src, char, Span>) -> Self {
        match value.reason() {
            chumsky::error::RichReason::ExpectedFound { expected, found } => {
                let expected = expected
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let found = found
                    .map(|x| x.to_string())
                    .unwrap_or_else(|| "nothing".into());

                CompileError::UnexpectedToken {
                    expected,
                    found,
                    span: span_to_miette(*value.span()),
                }
            }
            chumsky::error::RichReason::Custom(_) => todo!(),
        }
    }
}

impl<'src> From<Rich<'src, Token<'src>, Span>> for CompileError {
    fn from(value: Rich<'src, Token<'src>, Span>) -> Self {
        let span = *value.span();
        match value.into_reason() {
            chumsky::error::RichReason::ExpectedFound { expected, found } => {
                let expected = if expected.is_empty() {
                    "something".to_string()
                } else {
                    expected
                        .iter()
                        .map(|token| format!("{token:?}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                };

                let found = found
                    .map(|token| format!("{token:?}"))
                    .unwrap_or_else(|| "end of input".to_string());

                CompileError::UnexpectedToken {
                    expected,
                    found,
                    span: span_to_miette(span),
                }
            }
            chumsky::error::RichReason::Custom(msg) => CompileError::InvalidSyntax {
                span: span_to_miette(span),
                help: Some(msg.to_string()),
            },
        }
    }
}

// Helper to convert spans
pub fn span_to_miette(span: Span) -> SourceSpan {
    SourceSpan::new(span.start().into(), span.end() - span.start())
}
