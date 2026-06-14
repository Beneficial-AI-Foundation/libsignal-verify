import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-! Shared root models for the `rand_core` crate's trait decls. -/

/-- Trait declaration: [rand_core#1::RngCore]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.3/src/lib.rs', lines 130:0-130:17
    Name pattern: [rand_core#1::RngCore]
    Visibility: public -/
@[rust_trait "rand_core#1::RngCore"]
structure rand_core_1.RngCore (Self : Type) where
  next_u32 : Self → Result (Std.U32 × Self)
  next_u64 : Self → Result (Std.U64 × Self)
  fill_bytes : Self → Slice Std.U8 → Result (Self × (Slice Std.U8))

/-- Trait declaration: [rand_core#1::CryptoRng]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.3/src/lib.rs', lines 204:0-204:28
    Name pattern: [rand_core#1::CryptoRng]
    Visibility: public -/
@[rust_trait "rand_core#1::CryptoRng" (parentClauses := ["RngCoreInst"])]
structure rand_core_1.CryptoRng (Self : Type) where
  RngCoreInst : rand_core_1.RngCore Self
