use crate::{error::CompilerErrors, parser::parse};

pub mod ast;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod parsers;
pub mod semantic;

pub fn compile_src<'src>(src: &'src str) -> Result<(), CompilerErrors<'src>> {
    let _ast = parse(src)?;

    Ok(())
}
