use chumsky::{error::Rich, span::Span as _};
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::ast::{Span, Token};

#[derive(Error, Diagnostic, Debug)]
#[error("Errors occured during compilation")]
#[diagnostic()]
pub struct CompilerErrors<'src> {
    #[source_code]
    pub src: &'src str,
    #[related]
    pub errors: Vec<CompileError>,
}

impl<'src> CompilerErrors<'src> {
    pub fn new(src: &'src str, errors: impl Into<Vec<CompileError>>) -> Self {
        Self {
            src,
            errors: errors.into(),
        }
    }
}

#[derive(Error, Diagnostic, Debug)]
pub enum ParsingError {
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

#[derive(Clone, Error, Diagnostic, Debug)]
#[error("Semantic error")]
#[diagnostic()]
pub enum SemanticError {
    #[error("Conflicting type annotation")]
    #[diagnostic(
        code(types::conflicting_type_annotation),
        help("Consider removing the duplicate type annotation")
    )]
    ConflictingTypeAnnotation {
        #[label("duplicate here")]
        annotation: SourceSpan,
        #[label("...of this annotation")]
        duplicate_of: SourceSpan,
    },

    #[error("Attempted to annotate the type of a function that does not exist")]
    #[diagnostic(
        code(types::annotated_missing_function),
        help("Consider removing the annotation...")
    )]
    AnnotatedMissingFunction {
        #[label("...here")]
        span: SourceSpan,
    },

    #[error("Attempted to create type alias, which is currently not implemented")]
    #[diagnostic(
        code(types::unimplemented_alias),
        help("Consider removing the type alias")
    )]
    UnimplementedTypeAliasing {
        #[label]
        span: SourceSpan,
    },

    #[error("Attempted to create type that already exists: {name}")]
    #[diagnostic(
        code(types::type_exists),
        help("Consider removing the duplicate type definition")
    )]
    TypeExists {
        name: String,
        #[label]
        span: SourceSpan,
    },
}

#[derive(Error, Diagnostic, Debug)]
pub enum CompileError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Parsing(#[from] ParsingError),
    #[error(transparent)]
    #[diagnostic(transparent)]
    Semantic(#[from] SemanticError),
}

impl<'src> From<Rich<'src, char, Span>> for CompileError {
    fn from(value: Rich<'src, char, Span>) -> Self {
        match value.reason() {
            chumsky::error::RichReason::ExpectedFound { expected, found } => {
                let expected = expected
                    .iter()
                    .map(|x: &chumsky::error::RichPattern<'_, _>| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let found = found
                    .map(|x| x.to_string())
                    .unwrap_or_else(|| "nothing".into());

                ParsingError::UnexpectedToken {
                    expected,
                    found,
                    span: span_to_miette(*value.span()),
                }
                .into()
            }
            chumsky::error::RichReason::Custom(_) => todo!(),
        }
    }
}

impl<'src> From<Rich<'src, Token, Span>> for CompileError {
    fn from(value: Rich<'src, Token, Span>) -> Self {
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

                ParsingError::UnexpectedToken {
                    expected,
                    found,
                    span: span_to_miette(span),
                }
                .into()
            }
            chumsky::error::RichReason::Custom(msg) => ParsingError::InvalidSyntax {
                span: span_to_miette(span),
                help: Some(msg.to_string()),
            }
            .into(),
        }
    }
}

// Helper to convert spans
pub fn span_to_miette(span: Span) -> SourceSpan {
    SourceSpan::new(span.start().into(), span.end() - span.start())
}
