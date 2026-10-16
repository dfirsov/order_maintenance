//! Cross-check with the machine semantics: the same output as `lake exe xrun` (see
//! `lean/OM/Extract/XRun.lean`) for the generated code.
//!
//!     xrun OPS.txt

use om::Om;

fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| "ops.txt".into());
    let text = std::fs::read_to_string(path).expect("operation file");
    let mut om = Om::new(4);
    println!("init ok {} {}", om.m.cost, om.m.peak);
    for line in text.lines() {
        let w: Vec<&str> = line.split_whitespace().collect();
        let before = om.m.cost;
        let ans = match w.as_slice() {
            ["f"] => format!("h{}", om.insert_first()),
            ["a", x] => format!("h{}", om.insert_after(x.parse().unwrap())),
            ["d", x] => { om.delete(x.parse().unwrap()); "-".to_string() }
            ["o", x, y] => om.order(x.parse().unwrap(), y.parse().unwrap()).to_string(),
            _ => continue,
        };
        println!("ok {} {} {}", om.m.cost - before, ans, om.m.peak);
    }
}
