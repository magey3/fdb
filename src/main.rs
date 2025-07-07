fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    add(1, 2);
    println!("Hello, world!");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(1, 2), 3)
    }
}
