//! Report the tagged unions `promote::find_tagged_unions` recognises in a
//! `.lukb` module, with enough of the intermediate state to see WHY a sort was
//! or was not promoted. A measurement tool for the promotion slice.
use adsmt_ir_lukb::ast::{Item, Type};

fn main() {
    let p = std::env::args().nth(1).expect("usage: find_tagged_unions <file.lukb>");
    let src = std::fs::read_to_string(&p).expect("readable");
    let m = adsmt_ir_lukb::parse(&src).expect("parses");
    let us = adsmt_ir_lukb::promote::find_tagged_unions(&m);
    println!("recognised: {}", us.len());
    for u in &us {
        println!("  {} ({} ctors, {} axioms subsumed)", u.sort, u.ctors.len(), u.subsumed_axioms.len());
    }
    if std::env::args().any(|a| a == "-v") {
        for it in &m.items {
            if let Item::Sort(s) = it {
                let inj: Vec<&str> = m.items.iter().filter_map(|i| match i {
                    Item::Fn { name, params, ret, body: None }
                        if *ret == Type::Name(s.clone()) && params.len() == 1 => Some(name.as_str()),
                    _ => None,
                }).collect();
                println!("sort {s}: injections {inj:?}");
            }
        }
        let ax = m.items.iter().filter(|i| matches!(i, Item::Axiom(..))).count();
        println!("axioms: {ax}");
    }
}
