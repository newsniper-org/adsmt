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

// ── Term ────────────────────────────────────────────────────────

#[derive(Serialize, Deserialize)]
#[serde(tag = "t", rename_all = "snake_case")]
enum TermWire {
    Var { name: String, ty: Type },
    Const { name: String, ty: Type },
    App { fun: Box<TermWire>, arg: Box<TermWire> },
    Lam { var_name: String, var_ty: Type, body: Box<TermWire> },
}

impl TermWire {
    fn from_term(t: &Term) -> TermWire {
        match t.kind() {
            TermInner::Var(v) => TermWire::Var { name: v.name.clone(), ty: v.ty.clone() },
            TermInner::Const(c) => TermWire::Const { name: c.name.clone(), ty: c.ty.clone() },
            TermInner::App(f, x) => TermWire::App {
                fun: Box::new(TermWire::from_term(f)),
                arg: Box::new(TermWire::from_term(x)),
            },
            TermInner::Lam(v, body) => TermWire::Lam {
                var_name: v.name.clone(),
                var_ty: v.ty.clone(),
                body: Box::new(TermWire::from_term(body)),
            },
        }
    }
    fn into_term<E: serde::de::Error>(self) -> Result<Term, E> {
        match self {
            TermWire::Var { name, ty } => Ok(Term::var(&name, ty)),
            TermWire::Const { name, ty } => Ok(Term::const_(&name, ty)),
            TermWire::App { fun, arg } => {
                let f = fun.into_term::<E>()?;
                let x = arg.into_term::<E>()?;
                Term::app(f, x).map_err(|e| E::custom(e.to_string()))
            }
            TermWire::Lam { var_name, var_ty, body } => {
                let b = body.into_term::<E>()?;
                Ok(Term::lam(Var { name: var_name, ty: var_ty }, b))
            }
        }
    }
}

impl Serialize for Term {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        TermWire::from_term(self).serialize(s)
    }
}
impl<'de> Deserialize<'de> for Term {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        TermWire::deserialize(d)?.into_term()
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
}
