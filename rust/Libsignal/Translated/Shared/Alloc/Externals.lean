import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-! Shared external models for items from the Rust `alloc` crate. -/

/-- [alloc::vec::{alloc::vec::Vec<T>}::into_boxed_slice]:
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::into_boxed_slice] -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::into_boxed_slice"]
axiom alloc.vec.Vec.into_boxed_slice
  {T : Type} (A : Type) : alloc.vec.Vec T → Result (Slice T)
