//! Shared identifiers, diagnostics, configuration, and the compiler-neutral AST.
//!
//! The verification engine consumes this owned snapshot. It does not borrow `tsrs`
//! internal types. See `integration/tsrs/PIN` for the compiler revision this bridge
//! targets.

mod ast;
mod config;
mod diagnostic;
mod span;

pub use ast::*;
pub use config::*;
pub use diagnostic::*;
pub use span::*;

/// Verifier revision mixed into every proof-cache key.
pub const VERIFIER_VERSION: &str = "0.1.0";

/// Pinned `tsrs` revision the bridge is written against.
/// The host Rust toolchain cannot compile `tsrs` (it requires Rust 1.99), so the
/// engine invokes the `tsrs` CLI for typechecking and extracts a fail-closed subset.
pub const TSRS_PIN_COMMIT: &str = "3e9236361fa97a9e6c685f4833ac457ae2d8c50a";
pub const TSRS_PIN_VERSION: &str = "0.23.0";
pub const TSRS_TYPESCRIPT_VERSION: &str = "7.1.0-beta";
