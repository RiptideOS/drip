//! Types are resolved here and the AST is turned into HIR. Optimizations are
//! made in this step like constant expression evaluation before being lowered
//! and flattened to LIR.

pub mod ast_lowering;
pub mod hir;
pub mod primitive;
pub mod resolve;
pub mod ty;
pub mod type_check;
