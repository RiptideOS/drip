//! The backend of the compiler deals with LIR (Low-level Intermediate
//! Representation). In this form, many abstract concepts like loops and
//! conditionals are simplified to labels and jumps, expression trees are
//! flattened into ordered post fix operations, etc.
//!
//! To lower our HIR to LIR, several steps are required:
//! 1. Allocate room for stack variables, removing names.
//! 2. Iterate over block statements, simplifiying control structures and
//!    expression trees.

// mod lir;
