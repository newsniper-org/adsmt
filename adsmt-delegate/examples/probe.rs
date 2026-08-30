// Minimal probe: the delegation's context path, with an optional
// `set_option` applied first, to isolate what the CLI does differently.
use oxiz_solver::Context;
fn main() {
    let path = std::env::args().nth(1).expect("usage: probe <script.smt2> [opt=val ...]");
    let script = std::fs::read_to_string(&path).expect("read");
    let mut ctx = Context::new();
    for a in std::env::args().skip(2) {
        if let Some((k, v)) = a.split_once('=') {
            eprintln!("  set_option({k:?}, {v:?})");
            ctx.set_option(k, v);
        }
    }
    if let Ok(ms) = std::env::var("PROBE_TIMEOUT_MS") {
        if let Ok(v) = ms.parse::<u64>() { ctx.set_timeout_ms(v); }
    }
    match ctx.execute_script(&script) {
        Ok(out) => println!("out={out:?}  last_level={:?}", ctx.last_level()),
        Err(e) => println!("ERR {e:?}"),
    }
}
