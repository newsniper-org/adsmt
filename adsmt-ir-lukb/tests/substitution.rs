//! Surface substitution must not capture. The elaborator substitutes a match
//! scrutinee for a catch-all binder, an image binder's `f(x)` for its variable
//! and a call for a refinement's value; each of these used to put the
//! substituted term under any binder that happened to share a name with one
//! of its free variables:
//!
//!     goal: forall {y = f(v) | v > 0}. forall v: Int. v > y ==> v > 100
//!
//! read `y` as `f(v)` with the INNER `v`, and answered `unsat` for a goal z3
//! finds a counterexample to.
//!
//! The oracle is `let`, which the elaborator turns into a kernel `let` without
//! touching the surface: `match TO { x => P }` (a surface substitution) must be
//! definitionally equal to `let x = TO in P` (a kernel one). The terms are
//! generated from a four-name pool so that binders collide with the
//! substituted term's names on most draws.

use adsmt_ir::is_def_eq;
use adsmt_ir_lukb::elaborate;

const NAMES: [&str; 4] = ["x", "a", "b", "v"];

struct Gen(u64);

impl Gen {
    fn next(&mut self) -> u64 {
        // xorshift64*
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    fn pick(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn name(&mut self) -> &'static str {
        NAMES[self.pick(NAMES.len() as u64) as usize]
    }

    fn int(&mut self, depth: u32) -> String {
        if depth == 0 {
            return match self.pick(5) {
                0 => "1".to_string(),
                _ => self.name().to_string(),
            };
        }
        let d = depth - 1;
        match self.pick(6) {
            0 => format!("({} + {})", self.int(d), self.int(d)),
            1 => format!("g({})", self.int(d)),
            2 => {
                let n = self.name();
                format!("(let {n} = {} in {})", self.int(d), self.int(d))
            }
            3 => {
                let n = self.name();
                format!("(match {} {{ {n} => {} }})", self.int(d), self.int(d))
            }
            _ => self.int(0),
        }
    }

    fn prop(&mut self, depth: u32) -> String {
        if depth == 0 {
            return format!("{} > {}", self.int(1), self.int(1));
        }
        let d = depth - 1;
        match self.pick(8) {
            0 => {
                let n = self.name();
                format!("(forall {n}: Int. {})", self.prop(d))
            }
            1 => {
                let n = self.name();
                format!("(exists {n}: Int. {})", self.prop(d))
            }
            2 => {
                // a refined binder type: the predicate is under `w`.
                let n = self.name();
                format!("(forall {n}: {{w: Int | w > {}}}. {})", self.int(1), self.prop(d))
            }
            3 => {
                // an image binder binds its variable AND its preimage.
                let (n, m) = (self.name(), self.name());
                if n == m {
                    return self.prop(d);
                }
                format!("(forall {{{n} = g({m}) | {m} > {}}}. {})", self.int(1), self.prop(d))
            }
            4 => {
                let n = self.name();
                format!("(let {n} = {} in {})", self.int(1), self.prop(d))
            }
            5 => format!("({} and {})", self.prop(d), self.prop(d)),
            _ => format!("{} > {}", self.int(2), self.int(2)),
        }
    }
}

fn goal(body: &str) -> String {
    format!("fn g(z: Int): Int = z + 1\ngoal: forall a: Int, b: Int, v: Int, x: Int. {body}\n")
}

#[test]
fn a_catch_all_substitution_agrees_with_a_kernel_let_under_colliding_binders() {
    let mut g = Gen(0x9e37_79b9_7f4a_7c15);
    let (mut compared, mut refused) = (0, 0);
    for _ in 0..3000 {
        let to = g.int(2);
        let p = g.prop(3);
        let by_let = goal(&format!("let x = {to} in {p}"));
        let by_match = goal(&format!("match {to} {{ x => {p} }}"));
        let (l, m) = match (elaborate(&by_let), elaborate(&by_match)) {
            (Ok(l), Ok(m)) => (l, m),
            // a spelling the elaborator refuses (a refinement naming a later
            // binder, say) is refused on both paths alike.
            (Err(_), Err(_)) => {
                refused += 1;
                continue;
            }
            (Ok(_), Err(e)) => panic!("substitution refused what let admits: {e}\n{by_match}"),
            (Err(e), Ok(_)) => panic!("let refused what substitution admits: {e}\n{by_let}"),
        };
        assert!(
            is_def_eq(&l.env, &l.goals[0], &m.goals[0]),
            "capture:\n{by_match}\n  {}\nvs {by_let}\n  {}",
            m.goals[0],
            l.goals[0]
        );
        compared += 1;
    }
    assert!(compared > 2000, "only {compared} compared ({refused} refused on both paths)");
}

/// The image binder's variable unfolds under inner binders without capture —
/// the measured false proof above — and in the quantifier's own guards, where
/// it used to reach an OUTER constant of the same name.
#[test]
fn an_image_binder_unfolds_without_capture() {
    let pairs = [
        (
            "fn f(a: Int): Int = a + 1\n\
             goal: forall {y = f(v) | v > 0}. forall v: Int. v > y ==> v > 100",
            "fn f(a: Int): Int = a + 1\n\
             goal: forall v: Int. v > 0 ==> forall w: Int. w > f(v) ==> w > 100",
        ),
        (
            "fn f(a: Int): Int = a + 1\nconst y: Int\n\
             goal: forall {y = f(v) | v > 0}, (m: Int) > y. m > 100",
            "fn f(a: Int): Int = a + 1\nconst y: Int\n\
             goal: forall v: Int, m: Int. (v > 0 and m > f(v)) ==> m > 100",
        ),
    ];
    for (image, unfolded) in pairs {
        let a = elaborate(image).expect("image spelling elaborates");
        let b = elaborate(unfolded).expect("unfolded spelling elaborates");
        assert!(
            is_def_eq(&a.env, &a.goals[0], &b.goals[0]),
            "{image}\n  {}\nvs {unfolded}\n  {}",
            a.goals[0],
            b.goals[0]
        );
    }
}

/// A catch-all spelled like a constructor of another type is refused: the
/// substitution cannot tell the two readings apart.
#[test]
fn a_catch_all_spelled_like_a_constructor_is_refused() {
    let src = "data L = nil | cons(hd: Int, tl: L)\nconst k: Int\ngoal: match k { nil => k = k }\n";
    let Err(e) = elaborate(src) else { panic!("admitted: {src}") };
    assert!(e.to_string().contains("spelled like a constructor of `L`"), "{e}");
}
