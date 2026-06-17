import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-! Shared external models for the `uuid` crate. -/

/-- [uuid::Uuid]
Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/uuid-1.19.0/src/lib.rs'
Name pattern: [uuid::Uuid]
Doc: https://docs.rs/uuid/1.19.0/uuid/struct.Uuid.html -/
@[rust_type "uuid::Uuid"]
structure uuid.Uuid where
  bytes : Array Std.U8 16#usize

namespace uuid.Uuid

/-- [uuid::{uuid::Uuid}::as_bytes]:
Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/uuid-1.19.0/src/lib.rs', lines 790:4-790:42
Name pattern: [uuid::{uuid::Uuid}::as_bytes]
Docs: https://docs.rs/uuid/1.19.0/uuid/struct.Uuid.html#method.as_bytes -/
@[rust_fun "uuid::{uuid::Uuid}::as_bytes"]
def as_bytes (self : uuid.Uuid) : Result (Array Std.U8 16#usize) :=
  ok self.bytes

@[step]
theorem as_bytes_spec (self : uuid.Uuid) :
    as_bytes self ⦃ (result : Std.Array U8 16#usize) =>
      result = self.bytes ⦄ := by
  unfold as_bytes
  step*

end uuid.Uuid
