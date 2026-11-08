//! CNF decomposition now lives in `adsmt-cert::cnf`: the certificate checker
//! re-derives the clause set of a SAT-level refutation from the step's
//! premises with this very code, so the translator is part of what a
//! certificate is checked against (see `adsmt_cert::recheck`).

pub use adsmt_cert::cnf::*;
