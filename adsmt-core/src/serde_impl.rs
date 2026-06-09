//! Serde support for the kernel value types (feature `serde`).
//!
//! Serialization walks the structure into a plain tagged shadow;
//! deserialization rebuilds **through the hash-cons constructors**
//! ([`Term::var`] / [`Term::app`] / [`Type::app`] / …), so a
//! deserialized [`Term`] is properly interned in the deserializing
//! process — `==` is `Arc::ptr_eq` within that process, exactly as
//! for a natively-built term. The kind-checked constructors
//! (`Type::app`, `Term::app`) re-validate, so ill-formed wire data
//! is rejected at deserialize time rather than producing a
//! malformed term.
//!
//! [`Theorem`](crate::Theorem) is deliberately **not**
//! deserializable: it is a kernel-only trust token (a proven
//! sequent), and synthesising one from untrusted bytes would forge
//! a proof. Certificates store the publicly-constructable `Sequent`
//! (a `Term` pair) instead.

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::kind::Kind;
use crate::term::{Term, TermInner, Var};
use crate::ty::Type;

// ── Kind ────────────────────────────────────────────────────────

#[derive(Serialize, Deserialize)]
#[serde(tag = "k", rename_all = "snake_case")]
enum KindWire {
    Type,
    Arrow { dom: Box<KindWire>, cod: Box<KindWire> },
}

impl KindWire {
    fn from_kind(k: &Kind) -> KindWire {
        match k {
            Kind::Type => KindWire::Type,
            Kind::Arrow(a, b) => KindWire::Arrow {
                dom: Box::new(KindWire::from_kind(a)),
                cod: Box::new(KindWire::from_kind(b)),
            },
        }
    }
    fn into_kind(self) -> Kind {
        match self {
            KindWire::Type => Kind::Type,
            KindWire::Arrow { dom, cod } => Kind::arrow(dom.into_kind(), cod.into_kind()),
        }
    }
}

impl Serialize for Kind {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        KindWire::from_kind(self).serialize(s)
    }
}
impl<'de> Deserialize<'de> for Kind {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Ok(KindWire::deserialize(d)?.into_kind())
    }
}

// ── Type ────────────────────────────────────────────────────────

#[derive(Serialize, Deserialize)]
#[serde(tag = "t", rename_all = "snake_case")]
enum TypeWire {
    Var { name: String, kind: Kind },
    Const { name: String, kind: Kind },
    App { fun: Box<TypeWire>, arg: Box<TypeWire> },
}

impl TypeWire {
    fn from_type(ty: &Type) -> TypeWire {
        match ty {
            Type::Var(v) => TypeWire::Var { name: v.name.clone(), kind: v.kind.clone() },
            Type::Const(c) => TypeWire::Const { name: c.name.clone(), kind: c.kind.clone() },
            Type::App(f, a) => TypeWire::App {
                fun: Box::new(TypeWire::from_type(f)),
                arg: Box::new(TypeWire::from_type(a)),
            },
        }
    }
    fn into_type<E: serde::de::Error>(self) -> Result<Type, E> {
        match self {
            TypeWire::Var { name, kind } => Ok(Type::var(&name, kind)),
            TypeWire::Const { name, kind } => Ok(Type::const_(&name, kind)),
            TypeWire::App { fun, arg } => {
                let f = fun.into_type::<E>()?;
                let a = arg.into_type::<E>()?;
                Type::app(f, a).map_err(|e| E::custom(e.to_string()))
            }
        }
    }
}

impl Serialize for Type {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        TypeWire::from_type(self).serialize(s)
    }
}
impl<'de> Deserialize<'de> for Type {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        TypeWire::deserialize(d)?.into_type()
    }
}

// ── Term (flat hash-consed pool) ────────────────────────────────
//
// rc.33 (verus-fork "Gap B"): a `Term` used to serialize as a
// recursively *nested* shadow (`App { fun: Box<..>, arg: Box<..> }`),
// so the CBOR/JSON nesting depth grew with the term. A prelude-sized
// proof term then blew **ciborium's decode recursion limit** —
// `adsmt-emit-contract::decode` rejected the certificate before the
// Isabelle/Rocq render ever saw it — and shared subterms were
// re-serialized once per occurrence (the ~6.8 MB wire was mostly
// duplicated prelude subterms).
//
// Serialize the hash-consed `Term` DAG **flat** instead: a
// topologically-ordered pool of nodes whose children are `u32`
// indices into the pool, plus the root index. CBOR depth is then
// O(1) in term size (pool array → node struct → shallow `Kind`), and
// every distinct subterm/subtype is pooled exactly once (dedup, the
// same win as the AOT bank). Deserialization rebuilds the pool
// bottom-up **through the hash-cons constructors**, so the re-intern
// property is preserved (`==` is `Arc::ptr_eq`) and ill-formed wire
// data (bad kinds, forward/out-of-range indices) is rejected.

#[derive(Serialize, Deserialize)]
#[serde(tag = "t", rename_all = "snake_case")]
enum FlatType {
    Var { name: String, kind: Kind },
    Const { name: String, kind: Kind },
    App { fun: u32, arg: u32 },
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "t", rename_all = "snake_case")]
enum FlatTermNode {
    Var { name: String, ty: u32 },
    Const { name: String, ty: u32 },
    App { fun: u32, arg: u32 },
    Lam { var_name: String, var_ty: u32, body: u32 },
}

#[derive(Serialize, Deserialize)]
struct FlatTerm {
    types: Vec<FlatType>,
    terms: Vec<FlatTermNode>,
    root: u32,
}

/// Builds the deduplicated, topologically-ordered type + term pools.
#[derive(Default)]
struct PoolBuilder {
    types: Vec<FlatType>,
    type_idx: std::collections::HashMap<Type, u32>,
    terms: Vec<FlatTermNode>,
    term_idx: std::collections::HashMap<Term, u32>,
}

impl PoolBuilder {
    fn intern_type(&mut self, ty: &Type) -> u32 {
        if let Some(&i) = self.type_idx.get(ty) {
            return i;
        }
        let node = match ty {
            Type::Var(v) => FlatType::Var { name: v.name.clone(), kind: v.kind.clone() },
            Type::Const(c) => FlatType::Const { name: c.name.clone(), kind: c.kind.clone() },
            Type::App(f, a) => {
                let fun = self.intern_type(f);
                let arg = self.intern_type(a);
                FlatType::App { fun, arg }
            }
        };
        let i = self.types.len() as u32;
        self.types.push(node);
        self.type_idx.insert(ty.clone(), i);
        i
    }

    fn intern_term(&mut self, t: &Term) -> u32 {
        if let Some(&i) = self.term_idx.get(t) {
            return i;
        }
        let node = match t.kind() {
            TermInner::Var(v) => {
                let ty = self.intern_type(&v.ty);
                FlatTermNode::Var { name: v.name.clone(), ty }
            }
            TermInner::Const(c) => {
                let ty = self.intern_type(&c.ty);
                FlatTermNode::Const { name: c.name.clone(), ty }
            }
            TermInner::App(f, x) => {
                let fun = self.intern_term(f);
                let arg = self.intern_term(x);
                FlatTermNode::App { fun, arg }
            }
            TermInner::Lam(v, body) => {
                let var_ty = self.intern_type(&v.ty);
                let body = self.intern_term(body);
                FlatTermNode::Lam { var_name: v.name.clone(), var_ty, body }
            }
        };
        let i = self.terms.len() as u32;
        self.terms.push(node);
        self.term_idx.insert(t.clone(), i);
        i
    }
}

impl FlatTerm {
    fn from_term(t: &Term) -> FlatTerm {
        let mut b = PoolBuilder::default();
        let root = b.intern_term(t);
        FlatTerm { types: b.types, terms: b.terms, root }
    }

    fn into_term<E: serde::de::Error>(self) -> Result<Term, E> {
        // Rebuild bottom-up: the serializer emits children before
        // parents, so a backward index (`< current`) is always
        // resolvable and a forward/out-of-range one (`>= current`)
        // signals a malformed pool and is rejected by `get`.
        let mut types: Vec<Type> = Vec::with_capacity(self.types.len());
        for node in &self.types {
            let ty = match node {
                FlatType::Var { name, kind } => Type::var(name, kind.clone()),
                FlatType::Const { name, kind } => Type::const_(name, kind.clone()),
                FlatType::App { fun, arg } => {
                    let f = pool_get(&types, *fun, "type fun")?;
                    let a = pool_get(&types, *arg, "type arg")?;
                    Type::app(f, a).map_err(|e| E::custom(e.to_string()))?
                }
            };
            types.push(ty);
        }
        let ty_at = |i: u32| -> Result<Type, E> { pool_get(&types, i, "term ty") };
        let mut terms: Vec<Term> = Vec::with_capacity(self.terms.len());
        for node in &self.terms {
            let term = match node {
                FlatTermNode::Var { name, ty } => Term::var(name, ty_at(*ty)?),
                FlatTermNode::Const { name, ty } => Term::const_(name, ty_at(*ty)?),
                FlatTermNode::App { fun, arg } => {
                    let f = pool_get(&terms, *fun, "term fun")?;
                    let x = pool_get(&terms, *arg, "term arg")?;
                    Term::app(f, x).map_err(|e| E::custom(e.to_string()))?
                }
                FlatTermNode::Lam { var_name, var_ty, body } => {
                    let v = Var { name: var_name.clone(), ty: ty_at(*var_ty)? };
                    let b = pool_get(&terms, *body, "term lam body")?;
                    Term::lam(v, b)
                }
            };
            terms.push(term);
        }
        pool_get(&terms, self.root, "root")
    }
}

/// Resolve a pool index, erroring on an out-of-range / forward
/// reference (the pool is topologically ordered, so only backward
/// references are valid mid-rebuild).
fn pool_get<T: Clone, E: serde::de::Error>(pool: &[T], i: u32, what: &str) -> Result<T, E> {
    pool.get(i as usize)
        .cloned()
        .ok_or_else(|| E::custom(format!("flat term pool: {what} index {i} out of range or forward reference")))
}

impl Serialize for Term {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        FlatTerm::from_term(self).serialize(s)
    }
}
impl<'de> Deserialize<'de> for Term {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        FlatTerm::deserialize(d)?.into_term()
    }
}

#[cfg(test)]
mod tests {
    use crate::kind::Kind;
    use crate::term::{Term, Var};
    use crate::ty::Type;

    fn bool_ty() -> Type {
        Type::bool_()
    }

    #[test]
    fn kind_roundtrips() {
        let k = Kind::arrow(Kind::Type, Kind::arrow(Kind::Type, Kind::Type));
        let j = serde_json::to_string(&k).unwrap();
        let back: Kind = serde_json::from_str(&j).unwrap();
        assert_eq!(k, back);
    }

    #[test]
    fn type_roundtrips() {
        let ty = bool_ty();
        let j = serde_json::to_string(&ty).unwrap();
        let back: Type = serde_json::from_str(&j).unwrap();
        assert_eq!(ty, back);
    }

    #[test]
    fn term_roundtrips_and_is_reinterned() {
        // (and p q) shape via a binary const applied twice
        let p = Term::var("p", bool_ty());
        let q = Term::var("q", bool_ty());
        let conj = Term::mk_and(p.clone(), q.clone()).unwrap();
        let j = serde_json::to_string(&conj).unwrap();
        let back: Term = serde_json::from_str(&j).unwrap();
        // structural equality holds, and because deserialize
        // re-interns, `==` (Arc::ptr_eq) is true against the
        // natively-built term.
        assert_eq!(conj, back);
        let p2: Term = serde_json::from_str(&serde_json::to_string(&p).unwrap()).unwrap();
        assert_eq!(p, p2);
    }

    #[test]
    fn lambda_roundtrips() {
        let v = Var { name: "x".into(), ty: bool_ty() };
        let body = Term::var("x", bool_ty());
        let lam = Term::lam(v, body);
        let j = serde_json::to_string(&lam).unwrap();
        let back: Term = serde_json::from_str(&j).unwrap();
        assert_eq!(lam, back);
    }

    #[test]
    fn deep_app_spine_roundtrips_without_deep_nesting() {
        // rc.33 (Gap B): a deep left-nested App spine used to serialize
        // as deeply-nested CBOR/JSON (depth ∝ term size), blowing the
        // decoder's recursion limit. The flat pool round-trips it, and
        // the wire is a flat array — depth O(1) in term size.
        use super::FlatTerm;
        let int = Type::const_("Int", Kind::Type);
        let f = Term::const_(
            "f",
            Type::fun(int.clone(), int.clone()).unwrap(),
        );
        // f (f (f (… (f x)))), 500 deep
        let mut t = Term::var("x", int.clone());
        for _ in 0..500 {
            t = Term::app(f.clone(), t).unwrap();
        }
        let j = serde_json::to_string(&t).unwrap();
        let back: Term = serde_json::from_str(&j).unwrap();
        assert_eq!(t, back);
        // The serialized form is a flat pool, not a nested tree.
        let flat: FlatTerm = serde_json::from_str(&j).unwrap();
        assert_eq!(flat.terms.len(), 502, "x + 500 apps + f const");
    }

    #[test]
    fn shared_subterm_is_pooled_once() {
        // `(= big big)` shares `big`; the flat pool stores it once
        // (dedup), so the term count is far below the naive 2× count.
        use super::FlatTerm;
        let int = Type::const_("Int", Kind::Type);
        let g = Term::const_("g", Type::fun(int.clone(), int.clone()).unwrap());
        let mut big = Term::var("y", int.clone());
        for _ in 0..100 {
            big = Term::app(g.clone(), big).unwrap();
        }
        let eq = Term::mk_eq(big.clone(), big.clone()).unwrap();
        let j = serde_json::to_string(&eq).unwrap();
        let back: Term = serde_json::from_str(&j).unwrap();
        assert_eq!(eq, back);
        let flat: FlatTerm = serde_json::from_str(&j).unwrap();
        // big = y + 100 g-apps = 102 unique nodes; plus g, plus `=`
        // const, plus the two `=` applications. The duplicated `big`
        // is NOT counted twice (dedup): well under 2×102.
        assert!(
            flat.terms.len() < 150,
            "expected dedup (<150 nodes), got {}",
            flat.terms.len()
        );
    }

    #[test]
    fn deep_term_survives_ciborium_recursion_limit() {
        // rc.33 (Gap B): the exact path the emit pipeline failed on —
        // `ciborium::from_reader`. A 1000-deep term, which the old
        // nested shadow would have serialized as 1000-deep CBOR
        // (blowing ciborium's default recursion cap → the
        // `RecursionLimitExceeded` verus-fork hit), round-trips cleanly
        // through the flat pool.
        let int = Type::const_("Int", Kind::Type);
        let f = Term::const_("f", Type::fun(int.clone(), int.clone()).unwrap());
        let mut t = Term::var("x", int);
        for _ in 0..1000 {
            t = Term::app(f.clone(), t).unwrap();
        }
        let mut buf = Vec::new();
        ciborium::into_writer(&t, &mut buf).expect("CBOR encode");
        let back: Term = ciborium::from_reader(buf.as_slice()).expect("CBOR decode (no recursion-limit blow-up)");
        assert_eq!(t, back);
    }

    #[test]
    fn forward_reference_in_pool_is_rejected() {
        // A hand-built pool whose App references a not-yet-built index
        // must be rejected (soundness: no forward/out-of-range refs).
        let bad = r#"{"types":[{"t":"const","name":"Bool","kind":{"k":"type"}}],"terms":[{"t":"app","fun":1,"arg":1}],"root":0}"#;
        let r: Result<Term, _> = serde_json::from_str(bad);
        assert!(r.is_err(), "forward reference must be rejected");
    }
}
