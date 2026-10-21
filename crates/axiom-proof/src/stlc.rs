//! A very small simply typed lambda calculus (STLC) kernel.
//!
//! This is deliberately independent of the resolution checker. It gives Axiom
//! v4 a typed proof-term core and a concrete Curry–Howard bridge: a term is
//! accepted only if its inferred type matches the proposed proposition.

use std::collections::BTreeMap;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    Base(String),
    Arrow(Box<Type>, Box<Type>),
}

impl Type {
    pub fn base(name: impl Into<String>) -> Self {
        Type::Base(name.into())
    }

    pub fn arrow(from: Type, to: Type) -> Self {
        Type::Arrow(Box::new(from), Box::new(to))
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Base(b) => f.write_str(b),
            Type::Arrow(a, b) => write!(f, "({a} -> {b})"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Var(String),
    Const(String),
    Lam(String, Type, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn var(name: impl Into<String>) -> Self {
        Expr::Var(name.into())
    }

    pub fn lam(name: impl Into<String>, ty: Type, body: Expr) -> Self {
        Expr::Lam(name.into(), ty, Box::new(body))
    }

    pub fn app(f: Expr, x: Expr) -> Self {
        Expr::App(Box::new(f), Box::new(x))
    }
}

pub type Context = BTreeMap<String, Type>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StlcError {
    Unbound(String),
    Mismatch { expected: Type, found: Type },
    NotAFunction(Type),
    Arity(String),
}

impl fmt::Display for StlcError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StlcError::Unbound(v) => write!(f, "unbound variable {v}"),
            StlcError::Mismatch { expected, found } => {
                write!(f, "expected {expected}, found {found}")
            }
            StlcError::NotAFunction(t) => write!(f, "{t} is not a function type"),
            StlcError::Arity(m) => f.write_str(m),
        }
    }
}

impl std::error::Error for StlcError {}

/// Infer the type of `expr` in `ctx`.
pub fn infer_type(expr: &Expr, ctx: &Context) -> Result<Type, StlcError> {
    match expr {
        Expr::Var(v) => ctx
            .get(v)
            .cloned()
            .ok_or_else(|| StlcError::Unbound(v.clone())),
        Expr::Const(name) => Ok(Type::base(name.clone())),
        Expr::Lam(x, ty, body) => {
            let mut inner = ctx.clone();
            inner.insert(x.clone(), ty.clone());
            let body_ty = infer_type(body, &inner)?;
            Ok(Type::arrow(ty.clone(), body_ty))
        }
        Expr::App(f, x) => {
            let f_ty = infer_type(f, ctx)?;
            match f_ty {
                Type::Arrow(arg, out) => {
                    let x_ty = infer_type(x, ctx)?;
                    if *arg == x_ty {
                        Ok(*out)
                    } else {
                        Err(StlcError::Mismatch {
                            expected: *arg,
                            found: x_ty,
                        })
                    }
                }
                other => Err(StlcError::NotAFunction(other)),
            }
        }
    }
}

/// Check a proof term against a proposition (a type).
pub fn check_type(expr: &Expr, expected: &Type, ctx: &Context) -> Result<(), StlcError> {
    let found = infer_type(expr, ctx)?;
    if &found == expected {
        Ok(())
    } else {
        Err(StlcError::Mismatch {
            expected: expected.clone(),
            found,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a() -> Type {
        Type::base("A")
    }

    fn b() -> Type {
        Type::base("B")
    }

    #[test]
    fn identity_has_a_to_a() {
        let id = Expr::lam("x", a(), Expr::var("x"));
        assert_eq!(
            infer_type(&id, &Context::new()).unwrap(),
            Type::arrow(a(), a())
        );
    }

    #[test]
    fn k_combinator_types() {
        // \x:A. \y:B. x  :  A -> B -> A
        let k = Expr::lam("x", a(), Expr::lam("y", b(), Expr::var("x")));
        assert_eq!(
            infer_type(&k, &Context::new()).unwrap(),
            Type::arrow(a(), Type::arrow(b(), a()))
        );
    }

    #[test]
    fn application_checks_argument_type() {
        let id = Expr::lam("x", a(), Expr::var("x"));
        let bad = Expr::app(id, Expr::lam("y", b(), Expr::var("y")));
        assert!(matches!(
            infer_type(&bad, &Context::new()),
            Err(StlcError::Mismatch { .. })
        ));
    }

    #[test]
    fn unbound_variable_is_rejected() {
        assert_eq!(
            infer_type(&Expr::var("x"), &Context::new()),
            Err(StlcError::Unbound("x".into()))
        );
    }
}
