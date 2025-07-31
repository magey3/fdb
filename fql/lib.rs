use crate::{
    ast::desugar, ctx::CompileContext, error::CompilerErrors, parser::parse,
    type_checker::type_check,
};

pub mod ast;
pub mod ctx;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod type_checker;

pub fn compile_src<'src>(src: &'src str) -> Result<(), CompilerErrors<'src>> {
    let ctx = CompileContext::new();
    let mut ast = parse(&ctx, src);
    desugar(&ctx, &mut ast);
    let typed_ast = type_check(&ctx, ast);

    dbg!(typed_ast);

    Ok(())
}
