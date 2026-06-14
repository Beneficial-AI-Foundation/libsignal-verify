import Aeneas
import Libsignal.Translated.Shared.RandCore
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-! Shared root model for the `rand` crate's `Rng` trait decl. -/

/-- Trait declaration: [rand::rng::Rng]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand-0.9.4/src/rng.rs', lines 58:0-58:22
    Name pattern: [rand::rng::Rng]
    Visibility: public -/
@[rust_trait "rand::rng::Rng" (parentClauses := ["rand_core_1RngCoreInst"])]
structure rand.rng.Rng (Self : Type) where
  rand_core_1RngCoreInst : rand_core_1.RngCore Self
