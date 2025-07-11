use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Int(i64),
    Text(String),
}

#[derive(Debug, Clone)]
pub enum Column {
    Int(Vec<i64>),
    Text(Vec<String>),
}

#[derive(Debug, Clone, Copy)]
pub enum ColumnKind {
    Int,
    Text,
}

#[derive(Clone, Debug, Default)]
pub struct Table {
    pub name: String,
    pub row_count: usize,
    pub columns: HashMap<String, Column>,
}

#[derive(Debug, Clone)]
pub struct Row(pub HashMap<String, Value>);

// new wrapper
#[derive(Clone)]
pub struct Rows(pub Vec<Row>);

impl fmt::Display for Rows {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, row) in self.0.iter().enumerate() {
            writeln!(f, "row {i}: {row:?}")?;
        }
        Ok(())
    }
}

impl Table {
    pub fn new(name: impl ToString) -> Self {
        Self {
            name: name.to_string(),
            ..Default::default()
        }
    }

    pub fn add_column(&mut self, name: impl ToString, kind: ColumnKind) -> &mut Self {
        let column = match kind {
            ColumnKind::Int => Column::Int(Vec::new()),
            ColumnKind::Text => Column::Text(Vec::new()),
        };
        self.columns.insert(name.to_string(), column);
        self
    }

    pub fn insert(&mut self, row: Row) {
        for (k, v) in row.0 {
            let col = self.columns.get_mut(&k).expect("missing column in table");
            match (col, v) {
                (Column::Int(items), Value::Int(v)) => items.push(v),
                (Column::Text(items), Value::Text(v)) => items.push(v),
                _ => panic!("type mismatch!"),
            }
        }
        self.row_count += 1;
    }

    // changed return type here
    pub fn select(&self) -> Rows {
        let mut out = Vec::with_capacity(self.row_count);
        for i in 0..self.row_count {
            let mut map = HashMap::with_capacity(self.columns.len());
            for (col_name, col) in &self.columns {
                let v = match col {
                    Column::Int(items) => Value::Int(items[i]),
                    Column::Text(items) => Value::Text(items[i].clone()),
                };
                map.insert(col_name.clone(), v);
            }
            out.push(Row(map));
        }
        Rows(out)
    }
}

fn main() {
    let mut table = Table::new("users");
    table
        .add_column("id", ColumnKind::Int)
        .add_column("name", ColumnKind::Text);

    table.insert(Row(HashMap::from([
        ("id".to_string(), Value::Int(0)),
        ("name".to_string(), Value::Text("Joe Schmoe".to_string())),
    ])));
    table.insert(Row(HashMap::from([
        ("id".to_string(), Value::Int(1)),
        ("name".to_string(), Value::Text("Joe Biden".to_string())),
    ])));

    let rows = table.select();
    // each row on its own line
    println!("{rows}");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_insert_and_select_empty() {
        let mut table = Table::new("users");
        table
            .add_column("id", ColumnKind::Int)
            .add_column("name", ColumnKind::Text);
        let rows = table.select().0;
        assert!(rows.is_empty());
    }

    #[test]
    fn test_insert_and_select_values() {
        let mut table = Table::new("users");
        table
            .add_column("id", ColumnKind::Int)
            .add_column("name", ColumnKind::Text);

        table.insert(Row(HashMap::from([
            ("id".to_string(), Value::Int(42)),
            ("name".to_string(), Value::Text("Alice".to_string())),
        ])));
        table.insert(Row(HashMap::from([
            ("id".to_string(), Value::Int(7)),
            ("name".to_string(), Value::Text("Bob".to_string())),
        ])));

        let rows = table.select().0;
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].0.get("id"), Some(&Value::Int(42)));
        assert_eq!(
            rows[0].0.get("name"),
            Some(&Value::Text("Alice".to_string()))
        );
        assert_eq!(rows[1].0.get("id"), Some(&Value::Int(7)));
        assert_eq!(rows[1].0.get("name"), Some(&Value::Text("Bob".to_string())));
    }
    #[test]
    fn test_empty_rows_display() {
        let table = Table::new("users");
        let rows = table.select();
        assert_eq!(format!("{rows}"), "");
    }

    #[test]
    fn test_rows_display() {
        let mut table = Table::new("users");
        table
            .add_column("id", ColumnKind::Int)
            .add_column("name", ColumnKind::Text);

        table.insert(Row(HashMap::from([
            ("id".to_string(), Value::Int(0)),
            ("name".to_string(), Value::Text("Joe Schmoe".to_string())),
        ])));
        table.insert(Row(HashMap::from([
            ("id".to_string(), Value::Int(1)),
            ("name".to_string(), Value::Text("Joe Biden".to_string())),
        ])));

        let output = format!("{}", table.select());
        let lines: Vec<&str> = output.lines().collect();
        assert_eq!(lines.len(), 2);
        assert!(lines[0].starts_with("row 0: "));
        assert!(lines[0].contains("Int(0)"));
        assert!(lines[0].contains("Schmoe"));
        assert!(lines[1].starts_with("row 1: "));
        assert!(lines[1].contains("Int(1)"));
        assert!(lines[1].contains("Biden"));
    }
}
