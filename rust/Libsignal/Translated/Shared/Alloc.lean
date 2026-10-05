import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-! Shared external models for items from the Rust `alloc` crate. -/

def alloc.vec.Vec.Insts.CoreDefaultDefault.default (T : Type) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

def alloc.vec.Vec.as_slice {T : Type} (_ : Type) (value : alloc.vec.Vec T) : Result (Slice T) :=
  ok value.slice

/-- [alloc::vec::{alloc::vec::Vec<T>}::into_boxed_slice]:
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::into_boxed_slice] -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::into_boxed_slice"]
axiom alloc.vec.Vec.into_boxed_slice
  {T : Type} (A : Type) : alloc.vec.Vec T → Result (Slice T)
