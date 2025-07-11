use nom::{
    IResult, Parser,
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric0, multispace0, multispace1},
    combinator::{map, opt, recognize},
    multi::{many0, separated_list0, separated_list1},
    sequence::{delimited, preceded},
};
use nom_language::error::VerboseError;

/// AST Definitions

#[derive(Debug)]
pub struct Function {
    pub public: bool,
    pub name: String,
    pub params: Vec<Param>,
    pub body: Expr,
}

#[derive(Debug)]
pub struct Param {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug)]
pub struct Type(pub String);

#[derive(Debug)]
pub enum Expr {
    Identifier(String),
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    FunctionLiteral {
        params: Vec<String>,
        body: Box<Expr>,
    },
    BinaryOp {
        left: Box<Expr>,
        op: BinaryOp,
        right: Box<Expr>,
    },
    FieldAccess {
        target: Box<Expr>,
        field: String,
    },
    Pipeline {
        first: Box<Expr>,
        rest: Vec<Expr>,
    },
    Tuple(Vec<Expr>),
}

#[derive(Debug)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Equal,
    NotEqual,
    Less,
    Greater,
    LessOrEqual,
    GreaterOrEqual,
}

#[derive(Debug)]
enum PostfixOp {
    Call(Vec<Expr>),
    Field(String),
}

/// Skip surrounding whitespace
fn ws<'a, F, O>(inner: F) -> impl Parser<&'a str, Output = O, Error = VerboseError<&'a str>>
where
    F: Parser<&'a str, Output = O, Error = VerboseError<&'a str>>,
{
    // `delimited` returns some impl Parser<…>, so we just return it
    delimited(multispace0, inner, multispace0)
}
/// identifier = [A-Za-z][A-Za-z0-9]*
fn parse_identifier(input: &str) -> IResult<&str, String, VerboseError<&str>> {
    map(recognize((alpha1, alphanumeric0)), |s: &str| s.to_string()).parse(input)
}

/// type is just an identifier for now
fn parse_type(input: &str) -> IResult<&str, Type, VerboseError<&str>> {
    map(parse_identifier, Type).parse(input)
}

/// Param = name ':' Type
fn parse_param(input: &str) -> IResult<&str, Param, VerboseError<&str>> {
    map(
        (ws(parse_identifier), ws(tag(":")), ws(parse_type)),
        |(name, _, ty)| Param { name, ty },
    )
    .parse(input)
}

/// pub? fn name params… = expr
pub fn parse_function(input: &str) -> IResult<&str, Function, VerboseError<&str>> {
    map(
        (
            ws(opt(tag("pub"))),
            ws(tag("fn")),
            ws(parse_identifier),
            many0(ws(parse_param)),
            ws(tag("=")),
            ws(parse_expr),
        ),
        |(pub_opt, _, name, params, _, body)| Function {
            public: pub_opt.is_some(),
            name,
            params,
            body,
        },
    )
    .parse(input)
}

/// Top‐level expression parser (handles pipelines)
fn parse_expr(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    // pipeline := eq ( "|>" eq )*
    let (input, first) = parse_eq(input)?;
    let (input, rest) = many0(preceded(ws(tag("|>")), parse_eq)).parse(input)?;
    let expr = if rest.is_empty() {
        first
    } else {
        Expr::Pipeline {
            first: Box::new(first),
            rest,
        }
    };
    Ok((input, expr))
}

/// Parse equality: ==, !=
fn parse_eq(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let (input, init) = parse_cmp(input)?;
    let (input, ops) = many0((
        ws(alt((
            map(tag("=="), |_| BinaryOp::Equal),
            map(tag("!="), |_| BinaryOp::NotEqual),
        ))),
        parse_cmp,
    ))
    .parse(input)?;
    let expr = ops.into_iter().fold(init, |acc, (op, rhs)| Expr::BinaryOp {
        left: Box::new(acc),
        op,
        right: Box::new(rhs),
    });
    Ok((input, expr))
}

/// Parse comparisons: <, <=, >, >=
fn parse_cmp(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let (input, init) = parse_add(input)?;
    let (input, ops) = many0((
        ws(alt((
            map(tag("<="), |_| BinaryOp::LessOrEqual),
            map(tag(">="), |_| BinaryOp::GreaterOrEqual),
            map(tag("<"), |_| BinaryOp::Less),
            map(tag(">"), |_| BinaryOp::Greater),
        ))),
        parse_add,
    ))
    .parse(input)?;
    let expr = ops.into_iter().fold(init, |acc, (op, rhs)| Expr::BinaryOp {
        left: Box::new(acc),
        op,
        right: Box::new(rhs),
    });
    Ok((input, expr))
}

/// Parse addition/subtraction
fn parse_add(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let (input, init) = parse_mul(input)?;
    let (input, ops) = many0((
        ws(alt((
            map(tag("+"), |_| BinaryOp::Add),
            map(tag("-"), |_| BinaryOp::Sub),
        ))),
        parse_mul,
    ))
    .parse(input)?;
    let expr = ops.into_iter().fold(init, |acc, (op, rhs)| Expr::BinaryOp {
        left: Box::new(acc),
        op,
        right: Box::new(rhs),
    });
    Ok((input, expr))
}

/// Parse multiplication/division
fn parse_mul(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let (input, init) = parse_term(input)?;
    let (input, ops) = many0((
        ws(alt((
            map(tag("*"), |_| BinaryOp::Mul),
            map(tag("/"), |_| BinaryOp::Div),
        ))),
        parse_term,
    ))
    .parse(input)?;
    let expr = ops.into_iter().fold(init, |acc, (op, rhs)| Expr::BinaryOp {
        left: Box::new(acc),
        op,
        right: Box::new(rhs),
    });
    Ok((input, expr))
}

/// Parse the “atoms”: function literals, tuples/grouping, or identifiers
fn parse_atom(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    alt((
        parse_function_literal,
        parse_tuple_or_group,
        map(ws(parse_identifier), Expr::Identifier),
    ))
    .parse(input)
}

/// Postfix operators: call(arg,… ) or .field
fn parse_postfix_op(input: &str) -> IResult<&str, PostfixOp, VerboseError<&str>> {
    alt((
        map(
            delimited(
                ws(tag("(")),
                separated_list0(ws(tag(",")), parse_expr),
                ws(tag(")")),
            ),
            PostfixOp::Call,
        ),
        map(
            preceded(ws(tag(".")), ws(parse_identifier)),
            PostfixOp::Field,
        ),
    ))
    .parse(input)
}

/// Apply postfix operations left‐to‐right
fn parse_term(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let (input, init) = parse_atom(input)?;
    let (input, ops) = many0(parse_postfix_op).parse(input)?;
    let expr = ops.into_iter().fold(init, |acc, op| match op {
        PostfixOp::Call(args) => Expr::Call {
            func: Box::new(acc),
            args,
        },
        PostfixOp::Field(fld) => Expr::FieldAccess {
            target: Box::new(acc),
            field: fld,
        },
    });
    Ok((input, expr))
}

/// fn p1 p2 … = body
fn parse_function_literal(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    map(
        (
            ws(tag("fn")),
            ws(separated_list1(multispace1, parse_identifier)),
            ws(tag("=")),
            ws(parse_expr),
        ),
        |(_, params, _, body)| Expr::FunctionLiteral {
            params,
            body: Box::new(body),
        },
    )
    .parse(input)
}

/// (a, b, …) as Tuple, or (single) as grouping
fn parse_tuple_or_group(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    map(
        ws(delimited(
            tag("("),
            separated_list1(ws(tag(",")), parse_expr),
            tag(")"),
        )),
        |mut elems| {
            if elems.len() == 1 {
                elems.pop().unwrap()
            } else {
                Expr::Tuple(elems)
            }
        },
    )
    .parse(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multi_field_access() {
        let src = "pub fn f = x.a.b.c";
        let (_, func) = parse_function(src).unwrap();
        println!("{:#?}", func.body);
    }

    #[test]
    fn full_example() {
        let src = r#"
            pub fn queryName
                param1: Int
                param2: Float
                = table1
                |> filter (fn x = x.date > now)
                |> map (fn x = (x.id, x.name))
        "#;
        assert!(parse_function(src).is_ok());
    }
}
