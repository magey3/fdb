use crate::{
    ctx::CompileContext, desugar::desugar, error::CompilerErrors, parser::parse,
    type_checker::type_check,
};

pub mod ast;
pub mod ctx;
pub mod desugar;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod type_checker;

pub fn compile_src<'src>(src: &'src str) -> Result<(), CompilerErrors<'src>> {
    let ctx = CompileContext::new();
    let ast = parse(&ctx, src);
    let desugared_ast = desugar(&ctx, ast);
    let typed_ast = type_check(&ctx, desugared_ast);

    dbg!(typed_ast);

    Ok(())
}
