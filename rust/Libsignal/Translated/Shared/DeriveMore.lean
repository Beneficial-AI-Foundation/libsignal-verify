import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-! Shared root model for `derive_more`'s TryFromReprError. -/

/-- [derive_more::convert::try_from::TryFromReprError]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/derive_more-2.1.1/src/convert.rs', lines 17:4-17:34
    Name pattern: [derive_more::convert::try_from::TryFromReprError]
    Visibility: public -/
@[rust_type "derive_more::convert::try_from::TryFromReprError"]
structure derive_more.convert.try_from.TryFromReprError (T : Type) where
  input : T
