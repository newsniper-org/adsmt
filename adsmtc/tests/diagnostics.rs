// A module the face cannot elaborate is answered `unknown` — sound, but it
// used to be answered SILENTLY: the reason was printed only under
// `ADSMT_LUKB_DEBUG`, so an unknown symbol, or a refinement binder refused
// because it would capture a name, looked exactly like a goal the solver gave
// up on. The reason now goes to stderr; the verdict line does not change.

use std::io::Write;
use std::process::{Command, Stdio};

fn run(src: &str) -> (String, String, i32) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_adsmtc"))
        .env("ADSMT_NO_DELEGATION", "1")
        .env_remove("ADSMT_LUKB_DEBUG")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("adsmtc runs");
    child.stdin.take().unwrap().write_all(src.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    (
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
        out.status.code().unwrap_or(-1),
    )
}

#[test]
fn an_unknown_symbol_says_why_it_is_unknown() {
    let (out, err, code) = run("goal: zz > 0\n");
    assert_eq!(out.trim(), "unknown");
    assert_eq!(code, 2);
    assert!(err.contains("lu-kb: cannot elaborate") && err.contains("zz"), "stderr: {err:?}");
}

#[test]
fn a_refused_refinement_binder_says_why() {
    let (out, err, _) = run("const x: Int\ngoal: forall x: {v: Int | v > x}. x > 0\n");
    assert_eq!(out.trim(), "unknown");
    assert!(err.contains("lu-kb: cannot elaborate") && err.contains("rename"), "stderr: {err:?}");
}

#[test]
fn a_module_that_elaborates_prints_nothing_on_stderr() {
    let (out, err, code) = run("const x: Int\naxiom: x > 5\ngoal: x > 3\n");
    assert_eq!((out.trim(), code), ("unsat", 1));
    assert_eq!(err, "");
}

#[test]
fn the_debug_line_keeps_its_old_text() {
    // verus-fork's corpus manifest collects this text as the stage-bail reason.
    let mut child = Command::new(env!("CARGO_BIN_EXE_adsmtc"))
        .env("ADSMT_NO_DELEGATION", "1")
        .env("ADSMT_LUKB_DEBUG", "1")
        .stdin(Stdio::piped())
        .stderr(Stdio::piped())
        .stdout(Stdio::null())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(b"goal: zz > 0\n").unwrap();
    let err = String::from_utf8(child.wait_with_output().unwrap().stderr).unwrap();
    assert!(err.contains("[lukb-dbg] elaborate failed: "), "stderr: {err:?}");
}
