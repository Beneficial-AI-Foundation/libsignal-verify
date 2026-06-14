import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-! Shared external models for items from the Rust `core` crate.

These are axiomatised in more than one per-crate translation, so they live here
once and are imported where used — otherwise each translation lib would declare
the same name and they would collide when built into one import graph.
Only models with no dependency on a translation lib's `Types`/`Funs` belong here. -/

/-- [core::num::error::TryFromIntError]
    Name pattern: [core::num::error::TryFromIntError] -/
@[rust_type "core::num::error::TryFromIntError"]
axiom core.num.error.TryFromIntError : Type

/-- [core::option::{core::option::Option<T>}::map]:
    Name pattern: [core::option::{core::option::Option<@T>}::map] -/
@[rust_fun "core::option::{core::option::Option<@T>}::map"]
axiom core.option.Option.map
  {T : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
  core.ops.function.FnOnce F T U) :
  Option T → F → Result (Option U)

/-- [core::option::{Try for Option<T>}::branch] -/
@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
axiom core.option.Option.Insts.CoreOpsTry_traitTry.branch
  {T : Type} :
  Option T → Result (core.ops.control_flow.ControlFlow (Option
    core.convert.Infallible) T)

/-- [core::option::{FromResidual<Option<Infallible>> for Option<T>}::from_residual] -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
axiom
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
  (T : Type) : Option core.convert.Infallible → Result (Option T)

/-- [core::result::{Try for Result<T, E>}::branch] -/
@[rust_fun
  "core::result::{core::ops::try_trait::Try<core::result::Result<@T, @E>>}::branch"]
axiom core.result.Result.Insts.CoreOpsTry_traitTry.branch
  {T : Type} {E : Type} :
  core.result.Result T E → Result (core.ops.control_flow.ControlFlow
    (core.result.Result core.convert.Infallible E) T)

/-- [core::result::{FromResidual<Result<Infallible, E>> for Result<T, F>}::from_residual] -/
@[rust_fun
  "core::result::{core::ops::try_trait::FromResidual<core::result::Result<@T, @F>, core::result::Result<core::convert::Infallible, @E>>}::from_residual"]
axiom
  core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
  (T : Type) {E : Type} {F : Type} (convertFromInst : core.convert.From F E) :
  core.result.Result core.convert.Infallible E → Result (core.result.Result T
    F)
