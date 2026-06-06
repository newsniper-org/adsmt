use std::fmt;
use std::sync::Arc;

use indexmap::IndexMap;

use crate::error::{KernelError, KernelResult};
use crate::kind::Kind;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TyVar {
    pub name: String,
    pub kind: Kind,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TyConst {
    pub name: String,
    pub kind: Kind,
}

/// A type in predicative rank-1 polymorphic HOL with HKT.
///
/// Type-level lambda is intentionally absent (FOU at type level).
///
/// `PartialEq` is hand-rolled (rc.22 e.2) to add an
/// `Arc::ptr_eq` short-circuit on every recursive arm.  The
/// derived structural `Eq` would deref through every
/// `Arc<Type>` and re-enter `Type::eq` even when both sides
/// share one Arc — the verus_smoke flamegraph (2026-06-06)
/// attributed 17.20 % of cycles to that recursion.  Soundness
/// is preserved by the `||` fallback to the existing
/// structural comparison.  `Hash` is still derived because the
/// hand-rolled eq returns identical results to the derived
/// shape; the `Arc::ptr_eq` branch is purely a performance
/// short-circuit and does not change the equivalence relation.
#[derive(Clone, Debug, Eq, Hash)]
pub enum Type {
    Var(Arc<TyVar>),
    Const(Arc<TyConst>),
    App(Arc<Type>, Arc<Type>),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Var(a), Type::Var(b)) => Arc::ptr_eq(a, b) || **a == **b,
            (Type::Const(a), Type::Const(b)) => Arc::ptr_eq(a, b) || **a == **b,
            (Type::App(fa, xa), Type::App(fb, xb)) => {
                (Arc::ptr_eq(fa, fb) || **fa == **fb)
                    && (Arc::ptr_eq(xa, xb) || **xa == **xb)
            }
            _ => false,
        }
    }
}

impl Type {
    pub fn var(name: &str, kind: Kind) -> Type {
        Type::Var(Arc::new(TyVar { name: name.into(), kind }))
    }

    pub fn const_(name: &str, kind: Kind) -> Type {
        Type::Const(Arc::new(TyConst { name: name.into(), kind }))
    }

    /// Kind-checked application.
    pub fn app(f: Type, a: Type) -> KernelResult<Type> {
        let fk = f.kind_of();
        let ak = a.kind_of();
        match fk {
            Kind::Arrow(dom, _) if *dom == ak => Ok(Type::App(Arc::new(f), Arc::new(a))),
            Kind::Arrow(dom, _) => Err(KernelError::KindMismatch {
                expected: dom.to_string(),
                found: ak.to_string(),
            }),
            other => Err(KernelError::InvalidKindApplication {
                fun_kind: other.to_string(),
                arg_kind: ak.to_string(),
            }),
        }
    }

    pub fn kind_of(&self) -> Kind {
        match self {
            Type::Var(v) => v.kind.clone(),
            Type::Const(c) => c.kind.clone(),
            Type::App(f, _) => match f.kind_of() {
                Kind::Arrow(_, cod) => (*cod).clone(),
                Kind::Type => unreachable!("ill-kinded type slipped past app()"),
            },
        }
    }

    /// Built-in `Bool : Type`.
    pub fn bool_() -> Type {
        Type::const_("Bool", Kind::Type)
    }

    /// Built-in `-> : Type -> Type -> Type` type constructor.
    pub fn arrow_const() -> Type {
        Type::const_("->", Kind::first_order(2))
    }

    /// Build a function type `dom -> cod`.
    pub fn fun(dom: Type, cod: Type) -> KernelResult<Type> {
        Type::app(Type::app(Type::arrow_const(), dom)?, cod)
    }

    /// Decompose `dom -> cod`, if applicable.
    pub fn dest_fun(&self) -> Option<(Type, Type)> {
        if let Type::App(outer, cod) = self
            && let Type::App(arrow, dom) = &**outer
                && let Type::Const(c) = &**arrow
                    && c.name == "->" {
                        return Some(((**dom).clone(), (**cod).clone()));
                    }
        None
    }

    pub fn is_fun(&self) -> bool {
        self.dest_fun().is_some()
    }

    /// Collect free type variables in source order.
    pub fn free_vars(&self) -> Vec<Arc<TyVar>> {
        let mut out = Vec::new();
        self.collect_free(&mut out);
        out
    }

    fn collect_free(&self, out: &mut Vec<Arc<TyVar>>) {
        match self {
            Type::Var(v) => {
                if !out.iter().any(|w| **w == **v) {
                    out.push(v.clone());
                }
            }
            Type::Const(_) => {}
            Type::App(f, a) => {
                f.collect_free(out);
                a.collect_free(out);
            }
        }
    }

    /// Apply a type-variable substitution.
    pub fn subst(&self, sigma: &IndexMap<Arc<TyVar>, Type>) -> Type {
        if sigma.is_empty() {
            return self.clone();
        }
        match self {
            Type::Var(v) => sigma.get(v).cloned().unwrap_or_else(|| self.clone()),
            Type::Const(_) => self.clone(),
            Type::App(f, a) => Type::App(Arc::new(f.subst(sigma)), Arc::new(a.subst(sigma))),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((dom, cod)) = self.dest_fun() {
            if dom.is_fun() {
                return write!(f, "({dom}) -> {cod}");
            }
            return write!(f, "{dom} -> {cod}");
        }
        match self {
            Type::Var(v) => write!(f, "{}", v.name),
            Type::Const(c) => write!(f, "{}", c.name),
            Type::App(g, x) => match &**x {
                Type::App(..) => write!(f, "{g} ({x})"),
                _ => write!(f, "{g} {x}"),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn const_has_declared_kind() {
        assert_eq!(int_().kind_of(), Kind::Type);
    }

    #[test]
    fn app_kind_check() {
        let list = Type::const_("List", Kind::first_order(1));
        let list_int = Type::app(list, int_()).unwrap();
        assert_eq!(list_int.kind_of(), Kind::Type);
    }

    #[test]
    fn app_kind_mismatch_rejected() {
        let int_ = int_();
        let bool_ = Type::bool_();
        assert!(Type::app(int_, bool_).is_err());
    }

    #[test]
    fn fun_round_trip() {
        let t = Type::fun(int_(), int_()).unwrap();
        assert_eq!(t.kind_of(), Kind::Type);
        let (d, c) = t.dest_fun().unwrap();
        assert_eq!(d, int_());
        assert_eq!(c, int_());
    }

    #[test]
    fn subst_replaces_free_var() {
        let alpha = TyVar { name: "α".into(), kind: Kind::Type };
        let alpha_t = Type::Var(Arc::new(alpha.clone()));
        let mut sigma = IndexMap::new();
        sigma.insert(Arc::new(alpha), int_());
        assert_eq!(alpha_t.subst(&sigma), int_());
    }

    #[test]
    fn display_fun_right_associative() {
        let t = Type::fun(int_(), Type::fun(int_(), int_()).unwrap()).unwrap();
        assert_eq!(t.to_string(), "Int -> Int -> Int");
    }

    #[test]
    fn display_fun_left_parenthesized() {
        let inner = Type::fun(int_(), int_()).unwrap();
        let outer = Type::fun(inner, int_()).unwrap();
        assert_eq!(outer.to_string(), "(Int -> Int) -> Int");
    }

    #[test]
    fn hkt_partial_application() {
        // List : Type -> Type, partial application stays at kind `Type -> Type`
        let list = Type::const_("List", Kind::first_order(1));
        assert_eq!(list.kind_of(), Kind::first_order(1));
    }
}
