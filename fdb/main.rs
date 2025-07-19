use fql::parser::parse;

pub fn main() -> miette::Result<()> {
    let src = include_str!("../syntax.fql");

    let res = parse(src)?;

    println!("{:#?}", res);

    Ok(())
}
