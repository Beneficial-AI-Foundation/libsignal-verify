import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-! Shared external models for items from the Rust `core` crate.

Several per-crate translations require the same operations. Their definitions
and remaining external declarations live here once, so imports share one model.
Only models independent of a translation library's `Types`/`Funs` belong here. -/

/-- [core::num::error::TryFromIntError]
    Name pattern: [core::num::error::TryFromIntError] -/
-- Alias of the backend library's definition.
@[rust_type "core::num::error::TryFromIntError"]
abbrev core.num.error.TryFromIntError := Aeneas.Std.core.num.error.TryFromIntError

/-- [core::option::{core::option::Option<T>}::map]:
    Name pattern: [core::option::{core::option::Option<@T>}::map] -/
@[rust_fun "core::option::{core::option::Option<@T>}::map"]
def core.option.Option.map
  {T : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
  core.ops.function.FnOnce F T U) (value : Option T) (f : F) : Result (Option U) :=
  match value with
  | none => ok none
  | some x => do
    let y ← opsfunctionFnOnceFTupleTUInst.call_once f x
    ok (some y)

def core.mem.take {T : Type} (defaultInst : core.default.Default T) (value : T) :
    Result (T × T) := do
  let replacement ← defaultInst.default
  ok (value, replacement)

def core.option.Option.as_ref {T : Type} (value : Option T) : Result (Option T) :=
  ok value

def core.option.OptionResult.transpose {T E : Type} (value : Option (core.result.Result T E)) :
    Result (core.result.Result (Option T) E) :=
  match value with
  | none => ok (.Ok none)
  | some (.Ok x) => ok (.Ok (some x))
  | some (.Err e) => ok (.Err e)

/-- [core::option::{Try for Option<T>}::branch] -/
@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
axiom core.option.Option.Insts.CoreOpsTry_traitTry.branch
  {T : Type} :
  Option T → Result (core.ops.control_flow.ControlFlow (Option
    Never) T)

/-- [core::option::{FromResidual<Option<!>> for Option<T>}::from_residual] -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>}::from_residual"]
axiom
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
  (T : Type) : Option Never → Result (Option T)

/-- [core::result::{Try for Result<T, E>}::branch] -/
@[rust_fun
  "core::result::{core::ops::try_trait::Try<core::result::Result<@T, @E>>}::branch"]
axiom core.result.Result.Insts.CoreOpsTry_traitTry.branch
  {T : Type} {E : Type} :
  core.result.Result T E → Result (core.ops.control_flow.ControlFlow
    (core.result.Result Never E) T)

/-- [core::result::{FromResidual<Result<!, E>> for Result<T, F>}::from_residual] -/
@[rust_fun
  "core::result::{core::ops::try_trait::FromResidual<core::result::Result<@T, @F>, core::result::Result<!, @E>>}::from_residual"]
axiom
  core.result.Result.Insts.CoreOpsTry_traitFromResidualResultNeverE.from_residual
  (T : Type) {E : Type} {F : Type} (convertFromInst : core.convert.From F E) :
  core.result.Result Never E → Result (core.result.Result T F)
