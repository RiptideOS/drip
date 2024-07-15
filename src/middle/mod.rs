//! Types are resolved here and the AST is turned into HIR. Optimizations are
//! made in this step like constant expression evaluation before being lowered
//! and flattened to LIR.

pub mod hir;
