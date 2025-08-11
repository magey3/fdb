use fql::compile_src;

pub fn main() -> miette::Result<()> {
    compile_src(include_str!("../infer.fql"))?;
    Ok(())
}
