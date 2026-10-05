-- [libsignal_protocol]: external functions.
import Aeneas
import Libsignal.Translated.Protocol.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open libsignal_protocol

/-- [core::convert::{impl core::convert::AsRef<U> for &'_0 T}::as_ref]:
    Source: '/rustc/library/core/src/convert/mod.rs', lines 719:4-719:26
    Name pattern: [core::convert::{core::convert::AsRef<&'0 @T, @U>}::as_ref]
    Visibility: public -/
@[rust_fun "core::convert::{core::convert::AsRef<&'0 @T, @U>}::as_ref"]
axiom Shared0T.Insts.CoreConvertAsRef.as_ref
  {T : Type} {U : Type} (AsRefInst : core.convert.AsRef T U) : T → Result U

/-- [core::convert::{impl core::convert::Into<U> for T}::{impl core::ops::function::FnOnce<(T,), U> for core::convert::{impl core::convert::Into<U> for T}::into<T, U>[TraitClause0]}::call_once]:
    Source: '/rustc/library/core/src/convert/mod.rs', lines 779:4-779:22
    Name pattern: [core::convert::{core::convert::Into<@T, @U>}::{core::ops::function::FnOnce<@, (@T), @U>}::call_once]
    Visibility: public -/
@[rust_fun
  "core::convert::{core::convert::Into<@T, @U>}::{core::ops::function::FnOnce<@, (@T), @U>}::call_once"]
-- Calling a function item applies it (the template's type lacks parentheses).
def P.Insts.CoreOpsFunctionFnOnceTupleTU.call_once
  {T : Type} {U : Type} (FromInst : core.convert.From U T) :
  (T → Result U) → T → Result U :=
  fun f x => f x

/-- [core::convert::{impl core::convert::AsRef<[T]> for [T]}::as_ref]:
    Source: '/rustc/library/core/src/convert/mod.rs', lines 834:4-834:28
    Name pattern: [core::convert::{core::convert::AsRef<[@T], [@T]>}::as_ref]
    Visibility: public -/
@[rust_fun "core::convert::{core::convert::AsRef<[@T], [@T]>}::as_ref"]
axiom Slice.Insts.CoreConvertAsRefSlice.as_ref
  {T : Type} : Slice T → Result (Slice T)

/-- [core::convert::num::{impl core::convert::TryFrom<u32, core::num::error::TryFromIntError> for u8}::try_from]:
    Source: '/rustc/library/core/src/convert/num.rs', lines 383:12-383:64
    Name pattern: [core::convert::num::{core::convert::TryFrom<u8, u32, core::num::error::TryFromIntError>}::try_from]
    Visibility: public -/
@[rust_fun
  "core::convert::num::{core::convert::TryFrom<u8, u32, core::num::error::TryFromIntError>}::try_from"]
def U8.Insts.CoreConvertTryFromU32TryFromIntError.try_from
  (i : Std.U32) :
  Result (core.result.Result Std.U8 core.num.error.TryFromIntError) :=
  core.num.tryFromUScalar .U8 i

/-- [core::convert::num::{impl core::convert::TryFrom<u128, core::num::error::TryFromIntError> for u64}::try_from]:
    Source: '/rustc/library/core/src/convert/num.rs', lines 383:12-383:64
    Name pattern: [core::convert::num::{core::convert::TryFrom<u64, u128, core::num::error::TryFromIntError>}::try_from]
    Visibility: public -/
@[rust_fun
  "core::convert::num::{core::convert::TryFrom<u64, u128, core::num::error::TryFromIntError>}::try_from"]
axiom U64.Insts.CoreConvertTryFromU128TryFromIntError.try_from
  :
  Std.U128 → Result (core.result.Result Std.U64
    core.num.error.TryFromIntError)

/-- [core::fmt::{impl core::fmt::Display for str}::fmt]:
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 2965:4-2965:50
    Name pattern: [core::fmt::{core::fmt::Display<str>}::fmt]
    Visibility: public -/
@[rust_fun "core::fmt::{core::fmt::Display<str>}::fmt"]
axiom Str.Insts.CoreFmtDisplay.fmt
  :
  Str → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [core::hash::impls::{impl core::hash::Hash for u64}::hash]:
    Source: '/rustc/library/core/src/hash/mod.rs', lines 813:16-813:56
    Name pattern: [core::hash::impls::{core::hash::Hash<u64>}::hash]
    Visibility: public -/
@[rust_fun "core::hash::impls::{core::hash::Hash<u64>}::hash"]
axiom U64.Insts.CoreHashHash.hash
  {H : Type} (HasherInst : core.hash.Hasher H) : Std.U64 → H → Result H

/-- [core::hash::impls::{impl core::hash::Hash for u32}::hash]:
    Source: '/rustc/library/core/src/hash/mod.rs', lines 813:16-813:56
    Name pattern: [core::hash::impls::{core::hash::Hash<u32>}::hash]
    Visibility: public -/
@[rust_fun "core::hash::impls::{core::hash::Hash<u32>}::hash"]
axiom U32.Insts.CoreHashHash.hash
  {H : Type} (HasherInst : core.hash.Hasher H) : Std.U32 → H → Result H

/-- [core::hint::must_use]:
    Source: '/rustc/library/core/src/hint.rs', lines 613:0-613:39
    Name pattern: [core::hint::must_use]
    Visibility: public -/
@[rust_fun "core::hint::must_use"]
axiom core.hint.must_use {T : Type} : T → Result T

/-- [core::iter::traits::iterator::Iterator::position]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 3146:4-3149:37
    Name pattern: [core::iter::traits::iterator::Iterator::position]
    Visibility: public -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::position"]
axiom core.iter.traits.iterator.Iterator.position.default
  {Self : Type} {P : Type} {Clause0_Item : Type} (IteratorInst :
  core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutPTupleClause0_ItemBoolInst : core.ops.function.FnMut P
  Clause0_Item Bool) :
  Self → P → Result ((Option Std.Usize) × Self)

/-- [core::marker::{impl core::clone::Clone for core::marker::PhantomData<T>}::clone]:
    Source: '/rustc/library/core/src/marker.rs', lines 848:4-848:27
    Name pattern: [core::marker::{core::clone::Clone<core::marker::PhantomData<@T>>}::clone]
    Visibility: public -/
@[rust_fun
  "core::marker::{core::clone::Clone<core::marker::PhantomData<@T>>}::clone"]
axiom core.marker.PhantomData.Insts.CoreCloneClone.clone
  {T : Type} : core.marker.PhantomData T → Result (core.marker.PhantomData T)

-- (dropped axiom core.mem.take; provided by an imported sibling lib)

/-- [core::num::error::{impl core::fmt::Debug for core::num::error::TryFromIntError}::fmt]:
    Source: '/rustc/library/core/src/num/error.rs', lines 8:9-8:14
    Name pattern: [core::num::error::{core::fmt::Debug<core::num::error::TryFromIntError>}::fmt]
    Visibility: public -/
@[rust_fun
  "core::num::error::{core::fmt::Debug<core::num::error::TryFromIntError>}::fmt"]
axiom core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt
  :
  core.num.error.TryFromIntError → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

-- (dropped axiom core.option.Option.as_ref; provided by an imported sibling lib)

/-- [core::option::{core::option::Option<T>}::as_mut]:
    Source: '/rustc/library/core/src/option.rs', lines 766:4-766:52
    Name pattern: [core::option::{core::option::Option<@T>}::as_mut]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::as_mut"]
axiom core.option.Option.as_mut
  {T : Type} : Option T → Result ((Option T) × (Option T → Option T))

-- (dropped axiom core.option.Option.map; provided by an imported sibling lib)

/-- [core::option::{core::option::Option<T>}::ok_or_else]:
    Source: '/rustc/library/core/src/option.rs', lines 1361:4-1363:52
    Name pattern: [core::option::{core::option::Option<@T>}::ok_or_else]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or_else"]
axiom core.option.Option.ok_or_else
  {T : Type} {E : Type} {F : Type} (opsfunctionFnOnceFTupleEInst :
  core.ops.function.FnOnce F Unit E) :
  Option T → F → Result (core.result.Result T E)

/-- [core::option::{core::option::Option<T>}::as_deref]:
    Source: '/rustc/library/core/src/option.rs', lines 1388:4-1390:25
    Name pattern: [core::option::{core::option::Option<@T>}::as_deref]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::as_deref"]
axiom core.option.Option.as_deref
  {T : Type} {Clause0_Target : Type} (opsderefDerefInst : core.ops.deref.Deref
  T Clause0_Target) :
  Option T → Result (Option Clause0_Target)

/-- [core::option::{core::option::Option<T>}::and_then]:
    Source: '/rustc/library/core/src/option.rs', lines 1539:4-1541:61
    Name pattern: [core::option::{core::option::Option<@T>}::and_then]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::and_then"]
axiom core.option.Option.and_then
  {T : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTOptionInst :
  core.ops.function.FnOnce F T (Option U)) :
  Option T → F → Result (Option U)

/-- [core::option::{core::option::Option<T>}::zip]:
    Source: '/rustc/library/core/src/option.rs', lines 1983:4-1986:28
    Name pattern: [core::option::{core::option::Option<@T>}::zip]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::zip"]
axiom core.option.Option.zip
  {T : Type} {U : Type} : Option T → Option U → Result (Option (T × U))

-- (dropped axiom core.option.OptionResult.transpose; provided by an imported sibling lib)

/-- [core::option::{impl core::clone::Clone for core::option::Option<T>}::clone]:
    Source: '/rustc/library/core/src/option.rs', lines 2278:4-2278:27
    Name pattern: [core::option::{core::clone::Clone<core::option::Option<@T>>}::clone]
    Visibility: public -/
@[rust_fun
  "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
axiom core.option.Option.Insts.CoreCloneClone.clone
  {T : Type} (cloneCloneInst : core.clone.Clone T) :
  Option T → Result (Option T)

-- (dropped axiom core.option.Option.Insts.CoreOpsTry_traitTry.branch; provided by an imported sibling lib)

-- (dropped axiom core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual; provided by an imported sibling lib)

/-- [core::result::{core::result::Result<T, E>}::unwrap_or_default]:
    Source: '/rustc/library/core/src/result.rs', lines 1264:4-1267:28
    Name pattern: [core::result::{core::result::Result<@T, @E>}::unwrap_or_default]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::unwrap_or_default"]
axiom core.result.Result.unwrap_or_default
  {T : Type} {E : Type} (defaultDefaultInst : core.default.Default T) :
  core.result.Result T E → Result T

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a T> for core::slice::iter::Iter<'a, T>}::position]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 372:12-374:45
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::position]
    Visibility: public -/
-- Transcribes the slice iterator's `position`: apply the predicate to the
-- remaining elements in order and stop at the first `true`, consuming that
-- element. The index counts from the iterator's current position.
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::position"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.position
  {T : Type} {P : Type} (opsfunctionFnMutPTupleSharedATBoolInst :
  core.ops.function.FnMut P T Bool) (it : core.slice.iter.Iter T)
  (predicate : P) : Result ((Option Std.Usize) × (core.slice.iter.Iter T)) :=
  go (it.slice.val.drop it.i) predicate 0 >>= fun (found, consumed) =>
    let it := { it with i := it.i + consumed }
    match found with
    | none => ok (none, it)
    | some k =>
      if h : k < 2 ^ UScalarTy.Usize.numBits then ok (some (Usize.ofNatCore k h), it)
      else fail .integerOverflow
where
  go : List T → P → Nat → Result (Option Nat × Nat)
  | [], _, k => ok (none, k)
  | x :: xs, predicate, k => do
    let (b, predicate) ← opsfunctionFnMutPTupleSharedATBoolInst.call_mut predicate x
    if b then ok (some k, k + 1) else go xs predicate (k + 1)

/-- [core::slice::{[T]}::first_chunk]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 329:4-329:70
    Name pattern: [core::slice::{[@T]}::first_chunk]
    Visibility: public -/
-- The core library function: the first `N` elements, or `None` when the
-- slice is shorter.
@[rust_fun "core::slice::{[@T]}::first_chunk"]
def core.slice.Slice.first_chunk
  {T : Type} (N : Std.Usize) (s : Slice T) : Result (Option (Array T N)) :=
  if h : N.val ≤ s.length then
    ok (some (Array.from (s.val.take N.val)
      (by simp only [List.length_take, Slice.length] at *; omega)))
  else ok none

/-- [core::slice::{[T]}::split_last_chunk]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 449:4-449:83
    Name pattern: [core::slice::{[@T]}::split_last_chunk]
    Visibility: public -/
-- The core library function: the slice without its last `N` elements and
-- those elements, or `None` when the slice is shorter.
@[rust_fun "core::slice::{[@T]}::split_last_chunk"]
def core.slice.Slice.split_last_chunk
  {T : Type} (N : Std.Usize) (s : Slice T) :
  Result (Option ((Slice T) × (Array T N))) :=
  if h : N.val ≤ s.length then
    ok (some
      (Slice.from (s.val.take (s.length - N.val))
        (by have := s.property; simp only [List.length_take]; omega),
       Array.from (s.val.drop (s.length - N.val))
        (by simp only [List.length_drop, Slice.length] at *; omega)))
  else ok none

/-- [core::time::{impl core::default::Default for core::time::Duration}::default]:
    Source: '/rustc/library/core/src/time.rs', lines 79:60-79:67
    Name pattern: [core::time::{core::default::Default<core::time::Duration>}::default]
    Visibility: public -/
@[rust_fun
  "core::time::{core::default::Default<core::time::Duration>}::default"]
axiom core.time.Duration.Insts.CoreDefaultDefault.default
  : Result core.time.Duration

/-- [core::time::{core::time::Duration}::from_secs]:
    Source: '/rustc/library/core/src/time.rs', lines 224:4-224:49
    Name pattern: [core::time::{core::time::Duration}::from_secs]
    Visibility: public -/
@[rust_fun "core::time::{core::time::Duration}::from_secs"]
axiom core.time.Duration.from_secs : Std.U64 → Result core.time.Duration

/-- [core::time::{core::time::Duration}::from_millis]:
    Source: '/rustc/library/core/src/time.rs', lines 244:4-244:53
    Name pattern: [core::time::{core::time::Duration}::from_millis]
    Visibility: public -/
@[rust_fun "core::time::{core::time::Duration}::from_millis"]
axiom core.time.Duration.from_millis : Std.U64 → Result core.time.Duration

/-- [core::time::{core::time::Duration}::as_secs]:
    Source: '/rustc/library/core/src/time.rs', lines 514:4-514:38
    Name pattern: [core::time::{core::time::Duration}::as_secs]
    Visibility: public -/
@[rust_fun "core::time::{core::time::Duration}::as_secs"]
axiom core.time.Duration.as_secs : core.time.Duration → Result Std.U64

/-- [core::time::{core::time::Duration}::as_millis]:
    Source: '/rustc/library/core/src/time.rs', lines 601:4-601:41
    Name pattern: [core::time::{core::time::Duration}::as_millis]
    Visibility: public -/
@[rust_fun "core::time::{core::time::Duration}::as_millis"]
axiom core.time.Duration.as_millis : core.time.Duration → Result Std.U128

/-- [std::path::{impl core::ops::deref::Deref<std::path::Path> for std::path::PathBuf}::deref]:
    Source: '/rustc/library/std/src/path.rs', lines 2095:4-2095:28
    Name pattern: [std::path::{core::ops::deref::Deref<std::path::PathBuf, std::path::Path>}::deref]
    Visibility: public -/
@[rust_fun
  "std::path::{core::ops::deref::Deref<std::path::PathBuf, std::path::Path>}::deref"]
axiom std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref
  : std.path.PathBuf → Result std.path.Path

/-- [std::path::{std::path::Path}::display]:
    Source: '/rustc/library/std/src/path.rs', lines 3306:4-3306:40
    Name pattern: [std::path::{std::path::Path}::display]
    Visibility: public -/
@[rust_fun "std::path::{std::path::Path}::display"]
axiom std.path.Path.display : std.path.Path → Result std.path.Display

/-- [std::time::{impl core::clone::Clone for std::time::SystemTime}::clone]:
    Source: '/rustc/library/std/src/time.rs', lines 246:15-246:20
    Name pattern: [std::time::{core::clone::Clone<std::time::SystemTime>}::clone]
    Visibility: public -/
@[rust_fun "std::time::{core::clone::Clone<std::time::SystemTime>}::clone"]
axiom std.time.SystemTime.Insts.CoreCloneClone.clone
  : std.time.SystemTime → Result std.time.SystemTime

/-- [std::time::{impl core::fmt::Debug for std::time::SystemTimeError}::fmt]:
    Source: '/rustc/library/std/src/time.rs', lines 268:16-268:21
    Name pattern: [std::time::{core::fmt::Debug<std::time::SystemTimeError>}::fmt]
    Visibility: public -/
@[rust_fun "std::time::{core::fmt::Debug<std::time::SystemTimeError>}::fmt"]
axiom std.time.SystemTimeError.Insts.CoreFmtDebug.fmt
  :
  std.time.SystemTimeError → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [std::time::{std::time::SystemTime}::UNIX_EPOCH]
    Source: '/rustc/library/std/src/time.rs', lines 511:4-511:36
    Name pattern: [std::time::{std::time::SystemTime}::UNIX_EPOCH]
    Visibility: public -/
@[rust_const "std::time::{std::time::SystemTime}::UNIX_EPOCH"]
axiom std.time.SystemTime.UNIX_EPOCH : Result std.time.SystemTime

/-- [std::time::{std::time::SystemTime}::now]:
    Source: '/rustc/library/std/src/time.rs', lines 601:4-601:30
    Name pattern: [std::time::{std::time::SystemTime}::now]
    Visibility: public -/
@[rust_fun "std::time::{std::time::SystemTime}::now"]
axiom std.time.SystemTime.now : Result std.time.SystemTime

/-- [std::time::{std::time::SystemTime}::duration_since]:
    Source: '/rustc/library/std/src/time.rs', lines 630:4-630:90
    Name pattern: [std::time::{std::time::SystemTime}::duration_since]
    Visibility: public -/
@[rust_fun "std::time::{std::time::SystemTime}::duration_since"]
axiom std.time.SystemTime.duration_since
  :
  std.time.SystemTime → std.time.SystemTime → Result (core.result.Result
    core.time.Duration std.time.SystemTimeError)

/-- [std::time::{impl core::ops::arith::Add<core::time::Duration, std::time::SystemTime> for std::time::SystemTime}::add]:
    Source: '/rustc/library/std/src/time.rs', lines 746:4-746:45
    Name pattern: [std::time::{core::ops::arith::Add<std::time::SystemTime, core::time::Duration, std::time::SystemTime>}::add]
    Visibility: public -/
@[rust_fun
  "std::time::{core::ops::arith::Add<std::time::SystemTime, core::time::Duration, std::time::SystemTime>}::add"]
axiom std.time.SystemTime.Insts.CoreOpsArithAddDurationSystemTime.add
  : std.time.SystemTime → core.time.Duration → Result std.time.SystemTime

/-- [alloc::borrow::{impl alloc::borrow::ToOwned<T> for T}::to_owned]:
    Source: '/rustc/library/alloc/src/borrow.rs', lines 77:4-77:27
    Name pattern: [alloc::borrow::{alloc::borrow::ToOwned<@T, @T>}::to_owned]
    Visibility: public -/
@[rust_fun "alloc::borrow::{alloc::borrow::ToOwned<@T, @T>}::to_owned"]
axiom alloc.borrow.ToOwned.Blanket.to_owned
  {T : Type} (corecloneCloneInst : core.clone.Clone T) : T → Result T

/-- [alloc::boxed::convert::{impl core::convert::From<&'_0 [T]> for alloc::boxed::Box<[T]>}::from]:
    Source: '/rustc/library/alloc/src/boxed/convert.rs', lines 76:4-76:36
    Name pattern: [alloc::boxed::convert::{core::convert::From<Box<[@T]>, &'0 [@T]>}::from]
    Visibility: public -/
@[rust_fun
  "alloc::boxed::convert::{core::convert::From<Box<[@T]>, &'0 [@T]>}::from"]
axiom BoxSlice.Insts.CoreConvertFromShared0Slice.from
  {T : Type} (corecloneCloneInst : core.clone.Clone T) :
  Slice T → Result (Slice T)

/-- [alloc::boxed::{impl core::clone::Clone for alloc::boxed::Box<[T]>}::clone]:
    Source: '/rustc/library/alloc/src/boxed.rs', lines 2136:4-2136:27
    Name pattern: [alloc::boxed::{core::clone::Clone<Box<[@T]>>}::clone]
    Visibility: public -/
@[rust_fun "alloc::boxed::{core::clone::Clone<Box<[@T]>>}::clone"]
axiom BoxSlice.Insts.CoreCloneClone.clone
  {T : Type} {A : Type} (corecloneCloneInst : core.clone.Clone T)
  (corecloneCloneInst1 : core.clone.Clone A) :
  Slice T → Result (Slice T)

/-- [alloc::boxed::{impl core::convert::AsRef<T> for alloc::boxed::Box<T>}::as_ref]:
    Source: '/rustc/library/alloc/src/boxed.rs', lines 2429:4-2429:26
    Name pattern: [alloc::boxed::{core::convert::AsRef<Box<@T>, @T>}::as_ref]
    Visibility: public -/
@[rust_fun "alloc::boxed::{core::convert::AsRef<Box<@T>, @T>}::as_ref"]
axiom Box.Insts.CoreConvertAsRef.as_ref {T : Type} (A : Type) : T → Result T

/-- [alloc::collections::vec_deque::iter::{impl core::iter::traits::iterator::Iterator<&'a T> for alloc::collections::vec_deque::iter::Iter<'a, T>}::next]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/iter.rs', lines 92:4-92:39
    Name pattern: [alloc::collections::vec_deque::iter::{core::iter::traits::iterator::Iterator<alloc::collections::vec_deque::iter::Iter<'a, @T>, &'a @T>}::next]
    Visibility: public -/
@[rust_fun
  "alloc::collections::vec_deque::iter::{core::iter::traits::iterator::Iterator<alloc::collections::vec_deque::iter::Iter<'a, @T>, &'a @T>}::next"]
axiom
  alloc.collections.vec_deque.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
  {T : Type} :
  alloc.collections.vec_deque.iter.Iter T → Result ((Option T) ×
    (alloc.collections.vec_deque.iter.Iter T))

/-- [alloc::collections::vec_deque::{impl core::clone::Clone for alloc::collections::vec_deque::VecDeque<T, A>}::clone]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 120:4-120:27
    Name pattern: [alloc::collections::vec_deque::{core::clone::Clone<alloc::collections::vec_deque::VecDeque<@T, @A>>}::clone]
    Visibility: public -/
@[rust_fun
  "alloc::collections::vec_deque::{core::clone::Clone<alloc::collections::vec_deque::VecDeque<@T, @A>>}::clone"]
axiom alloc.collections.vec_deque.VecDeque.Insts.CoreCloneClone.clone
  {T : Type} {A : Type} (corecloneCloneInst : core.clone.Clone T)
  (corecloneCloneInst1 : core.clone.Clone A) :
  alloc.collections.vec_deque.VecDeque T A → Result
    (alloc.collections.vec_deque.VecDeque T A)

/-- [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<T, alloc::alloc::Global>}::with_capacity]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 868:4-868:56
    Name pattern: [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, alloc::alloc::Global>}::with_capacity]
    Visibility: public -/
@[rust_fun
  "alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, alloc::alloc::Global>}::with_capacity"]
axiom alloc.collections.vec_deque.VecDequeTGlobal.with_capacity
  (T : Type) :
  Std.Usize → Result (alloc.collections.vec_deque.VecDeque T Global)

/-- [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<T, A>}::len]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 1808:4-1808:30
    Name pattern: [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::len]
    Visibility: public -/
@[rust_fun
  "alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::len"]
axiom alloc.collections.vec_deque.VecDeque.len
  {T : Type} {A : Type} :
  alloc.collections.vec_deque.VecDeque T A → Result Std.Usize

/-- [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<T, A>}::push_back]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 2385:4-2385:41
    Name pattern: [alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::push_back]
    Visibility: public -/
@[rust_fun
  "alloc::collections::vec_deque::{alloc::collections::vec_deque::VecDeque<@T, @A>}::push_back"]
axiom alloc.collections.vec_deque.VecDeque.push_back
  {T : Type} {A : Type} :
  alloc.collections.vec_deque.VecDeque T A → T → Result
    (alloc.collections.vec_deque.VecDeque T A)

/-- [alloc::collections::vec_deque::{impl core::ops::index::Index<usize, T> for alloc::collections::vec_deque::VecDeque<T, A>}::index]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 3944:4-3944:39
    Name pattern: [alloc::collections::vec_deque::{core::ops::index::Index<alloc::collections::vec_deque::VecDeque<@T, @A>, usize, @T>}::index]
    Visibility: public -/
@[rust_fun
  "alloc::collections::vec_deque::{core::ops::index::Index<alloc::collections::vec_deque::VecDeque<@T, @A>, usize, @T>}::index"]
axiom alloc.collections.vec_deque.VecDeque.Insts.CoreOpsIndexIndexUsizeT.index
  {T : Type} {A : Type} :
  alloc.collections.vec_deque.VecDeque T A → Std.Usize → Result T

/-- [alloc::collections::vec_deque::{impl core::ops::index::IndexMut<usize, T> for alloc::collections::vec_deque::VecDeque<T, A>}::index_mut]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 3952:4-3952:51
    Name pattern: [alloc::collections::vec_deque::{core::ops::index::IndexMut<alloc::collections::vec_deque::VecDeque<@T, @A>, usize, @T>}::index_mut]
    Visibility: public -/
@[rust_fun
  "alloc::collections::vec_deque::{core::ops::index::IndexMut<alloc::collections::vec_deque::VecDeque<@T, @A>, usize, @T>}::index_mut"]
axiom
  alloc.collections.vec_deque.VecDeque.Insts.CoreOpsIndexIndexMutUsizeT.index_mut
  {T : Type} {A : Type} :
  alloc.collections.vec_deque.VecDeque T A → Std.Usize → Result (T × (T
    → alloc.collections.vec_deque.VecDeque T A))

/-- [alloc::collections::vec_deque::{impl core::iter::traits::collect::IntoIterator<&'a T, alloc::collections::vec_deque::iter::Iter<'a, T>> for &'a alloc::collections::vec_deque::VecDeque<T, A>}::into_iter]:
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 3981:4-3981:37
    Name pattern: [alloc::collections::vec_deque::{core::iter::traits::collect::IntoIterator<&'a alloc::collections::vec_deque::VecDeque<@T, @A>, &'a @T, alloc::collections::vec_deque::iter::Iter<'a, @T>>}::into_iter]
    Visibility: public -/
@[rust_fun
  "alloc::collections::vec_deque::{core::iter::traits::collect::IntoIterator<&'a alloc::collections::vec_deque::VecDeque<@T, @A>, &'a @T, alloc::collections::vec_deque::iter::Iter<'a, @T>>}::into_iter"]
axiom
  SharedAVecDeque.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
  {T : Type} {A : Type} :
  alloc.collections.vec_deque.VecDeque T A → Result
    (alloc.collections.vec_deque.iter.Iter T)

/-- [alloc::fmt::format]:
    Source: '/rustc/library/alloc/src/fmt.rs', lines 651:0-651:52
    Name pattern: [alloc::fmt::format]
    Visibility: public -/
@[rust_fun "alloc::fmt::format"]
axiom alloc.fmt.format : core.fmt.Arguments → Result String

/-- [alloc::str::{impl alloc::borrow::ToOwned<alloc::string::String> for str}::to_owned]:
    Source: '/rustc/library/alloc/src/str.rs', lines 252:4-252:32
    Name pattern: [alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned]
    Visibility: public -/
@[rust_fun
  "alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned"]
axiom Str.Insts.AllocBorrowToOwnedString.to_owned : Str → Result String

/-- [alloc::string::{impl core::clone::Clone for alloc::string::String}::clone]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2425:4-2425:27
    Name pattern: [alloc::string::{core::clone::Clone<alloc::string::String>}::clone]
    Visibility: public -/
@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
axiom alloc.string.String.Insts.CoreCloneClone.clone : String → Result String

-- (dropped axiom alloc.string.String.Insts.CoreOpsDerefDerefStr.deref; provided by an imported sibling lib)

/-- [alloc::string::{impl alloc::string::ToString for T}::to_string]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2965:4-2965:33
    Name pattern: [alloc::string::{alloc::string::ToString<@T>}::to_string]
    Visibility: public -/
@[rust_fun "alloc::string::{alloc::string::ToString<@T>}::to_string"]
axiom alloc.string.ToString.Blanket.to_string
  {T : Type} (corefmtDisplayInst : core.fmt.Display T) : T → Result String

-- (dropped axiom alloc.vec.Vec.into_boxed_slice; provided by an imported sibling lib)

-- (dropped axiom alloc.vec.Vec.as_slice; provided by an imported sibling lib)

/-- [alloc::vec::{alloc::vec::Vec<T>}::remove]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 2407:4-2407:47
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::remove]
    Visibility: public -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::remove"]
axiom alloc.vec.Vec.remove
  {T : Type} (A : Type) :
  alloc.vec.Vec T → Std.Usize → Result (T × (alloc.vec.Vec T))

/-- [alloc::vec::{alloc::vec::Vec<T>}::pop]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 2901:4-2901:38
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::pop]
    Visibility: public -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::pop"]
axiom alloc.vec.Vec.pop
  {T : Type} (A : Type) :
  alloc.vec.Vec T → Result ((Option T) × (alloc.vec.Vec T))

-- (dropped axiom alloc.vec.Vec.Insts.CoreDefaultDefault.default; provided by an imported sibling lib)

/-- [alloc::vec::{impl core::convert::AsRef<[T]> for alloc::vec::Vec<T>}::as_ref]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 4445:4-4445:28
    Name pattern: [alloc::vec::{core::convert::AsRef<alloc::vec::Vec<@T>, [@T]>}::as_ref]
    Visibility: public -/
@[rust_fun
  "alloc::vec::{core::convert::AsRef<alloc::vec::Vec<@T>, [@T]>}::as_ref"]
axiom alloc.vec.Vec.Insts.CoreConvertAsRefSlice.as_ref
  {T : Type} (A : Type) : alloc.vec.Vec T → Result (Slice T)

/-- [alloc::vec::{impl core::convert::From<&'_0 [T]> for alloc::vec::Vec<T>}::from]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 4467:4-4467:30
    Name pattern: [alloc::vec::{core::convert::From<alloc::vec::Vec<@T>, &'0 [@T]>}::from]
    Visibility: public -/
@[rust_fun
  "alloc::vec::{core::convert::From<alloc::vec::Vec<@T>, &'0 [@T]>}::from"]
axiom alloc.vec.Vec.Insts.CoreConvertFromShared0Slice.from
  {T : Type} (corecloneCloneInst : core.clone.Clone T) :
  Slice T → Result (alloc.vec.Vec T)

/-- [alloc::vec::{impl core::convert::From<alloc::boxed::Box<[T]>> for alloc::vec::Vec<T>}::from]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 4568:4-4568:35
    Name pattern: [alloc::vec::{core::convert::From<alloc::vec::Vec<@T>, Box<[@T]>>}::from]
    Visibility: public -/
@[rust_fun
  "alloc::vec::{core::convert::From<alloc::vec::Vec<@T>, Box<[@T]>>}::from"]
axiom alloc.vec.Vec.Insts.CoreConvertFromBoxSlice.from
  {T : Type} (A : Type) : Slice T → Result (alloc.vec.Vec T)

/-- [bytes::buf::buf_impl::{impl bytes::buf::buf_impl::Buf for &'_0 [u8]}::advance]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bytes-1.12.0/src/buf/buf_impl.rs', lines 2906:4-2906:37
    Name pattern: [bytes::buf::buf_impl::{bytes::buf::buf_impl::Buf<&'0 [u8]>}::advance]
    Visibility: public -/
@[rust_fun
  "bytes::buf::buf_impl::{bytes::buf::buf_impl::Buf<&'0 [u8]>}::advance"]
axiom Shared0SliceU8.Insts.BytesBufBuf_implBuf.advance
  : Slice Std.U8 → Std.Usize → Result (Slice Std.U8)

/-- [bytes::buf::buf_impl::{impl bytes::buf::buf_impl::Buf for &'_0 [u8]}::chunk]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bytes-1.12.0/src/buf/buf_impl.rs', lines 2901:4-2901:28
    Name pattern: [bytes::buf::buf_impl::{bytes::buf::buf_impl::Buf<&'0 [u8]>}::chunk]
    Visibility: public -/
@[rust_fun
  "bytes::buf::buf_impl::{bytes::buf::buf_impl::Buf<&'0 [u8]>}::chunk"]
axiom Shared0SliceU8.Insts.BytesBufBuf_implBuf.chunk
  : Slice Std.U8 → Result (Slice Std.U8)

/-- [bytes::buf::buf_impl::{impl bytes::buf::buf_impl::Buf for &'_0 [u8]}::remaining]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bytes-1.12.0/src/buf/buf_impl.rs', lines 2896:4-2896:32
    Name pattern: [bytes::buf::buf_impl::{bytes::buf::buf_impl::Buf<&'0 [u8]>}::remaining]
    Visibility: public -/
@[rust_fun
  "bytes::buf::buf_impl::{bytes::buf::buf_impl::Buf<&'0 [u8]>}::remaining"]
axiom Shared0SliceU8.Insts.BytesBufBuf_implBuf.remaining
  : Slice Std.U8 → Result Std.Usize

/-- [bytes::buf::buf_mut::{impl bytes::buf::buf_mut::BufMut for alloc::vec::Vec<u8>}::chunk_mut]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bytes-1.12.0/src/buf/buf_mut.rs', lines 1623:4-1623:47
    Name pattern: [bytes::buf::buf_mut::{bytes::buf::buf_mut::BufMut<alloc::vec::Vec<u8>>}::chunk_mut]
    Visibility: public -/
@[rust_fun
  "bytes::buf::buf_mut::{bytes::buf::buf_mut::BufMut<alloc::vec::Vec<u8>>}::chunk_mut"]
axiom alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.chunk_mut
  :
  alloc.vec.Vec Std.U8 → Result (bytes.buf.uninit_slice.UninitSlice ×
    (bytes.buf.uninit_slice.UninitSlice → alloc.vec.Vec Std.U8))

/-- [bytes::buf::buf_mut::{impl bytes::buf::buf_mut::BufMut for alloc::vec::Vec<u8>}::advance_mut]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bytes-1.12.0/src/buf/buf_mut.rs', lines 1607:4-1607:48
    Name pattern: [bytes::buf::buf_mut::{bytes::buf::buf_mut::BufMut<alloc::vec::Vec<u8>>}::advance_mut]
    Visibility: public -/
@[rust_fun
  "bytes::buf::buf_mut::{bytes::buf::buf_mut::BufMut<alloc::vec::Vec<u8>>}::advance_mut"]
axiom alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.advance_mut
  : alloc.vec.Vec Std.U8 → Std.Usize → Result (alloc.vec.Vec Std.U8)

/-- [bytes::buf::buf_mut::{impl bytes::buf::buf_mut::BufMut for alloc::vec::Vec<u8>}::remaining_mut]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bytes-1.12.0/src/buf/buf_mut.rs', lines 1601:4-1601:36
    Name pattern: [bytes::buf::buf_mut::{bytes::buf::buf_mut::BufMut<alloc::vec::Vec<u8>>}::remaining_mut]
    Visibility: public -/
@[rust_fun
  "bytes::buf::buf_mut::{bytes::buf::buf_mut::BufMut<alloc::vec::Vec<u8>>}::remaining_mut"]
axiom alloc.vec.VecU8.Insts.BytesBufBuf_mutBufMut.remaining_mut
  : alloc.vec.Vec Std.U8 → Result Std.Usize

/-- [hex::encode]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/hex-0.4.3/src/lib.rs', lines 259:0-259:48
    Name pattern: [hex::encode]
    Visibility: public -/
@[rust_fun "hex::encode"]
axiom hex.encode
  {T : Type} (coreconvertAsRefTSliceU8Inst : core.convert.AsRef T (Slice
  Std.U8)) :
  T → Result String

/-- [libsignal_core::address::{impl core::cmp::PartialEq<libsignal_core::address::ServiceId> for libsignal_core::address::ServiceId}::eq]:
    Source: 'rust/core/src/address.rs', lines 184:28-184:37
    Name pattern: [libsignal_core::address::{core::cmp::PartialEq<libsignal_core::address::ServiceId, libsignal_core::address::ServiceId>}::eq]
    Visibility: public -/
@[rust_fun
  "libsignal_core::address::{core::cmp::PartialEq<libsignal_core::address::ServiceId, libsignal_core::address::ServiceId>}::eq"]
axiom libsignal_core.address.ServiceId.Insts.CoreCmpPartialEqServiceId.eq
  :
  libsignal_core.address.ServiceId → libsignal_core.address.ServiceId →
    Result Bool

-- (dropped axiom libsignal_core.address.ServiceId.service_id_fixed_width_binary; provided by an imported sibling lib)

/-- [libsignal_core::address::{libsignal_core::address::ServiceId}::parse_from_service_id_string]:
    Source: 'rust/core/src/address.rs', lines 267:4-267:68
    Name pattern: [libsignal_core::address::{libsignal_core::address::ServiceId}::parse_from_service_id_string]
    Visibility: public -/
@[rust_fun
  "libsignal_core::address::{libsignal_core::address::ServiceId}::parse_from_service_id_string"]
axiom libsignal_core.address.ServiceId.parse_from_service_id_string
  : Str → Result (Option libsignal_core.address.ServiceId)

/-- [libsignal_core::address::{impl core::clone::Clone for libsignal_core::address::DeviceId}::clone]:
    Source: 'rust/core/src/address.rs', lines 683:15-683:20
    Name pattern: [libsignal_core::address::{core::clone::Clone<libsignal_core::address::DeviceId>}::clone]
    Visibility: public -/
@[rust_fun
  "libsignal_core::address::{core::clone::Clone<libsignal_core::address::DeviceId>}::clone"]
axiom libsignal_core.address.DeviceId.Insts.CoreCloneClone.clone
  : libsignal_core.address.DeviceId → Result libsignal_core.address.DeviceId

/-- [libsignal_core::address::{impl core::convert::From<libsignal_core::address::DeviceId> for u8}::from]:
    Source: 'rust/core/src/address.rs', lines 728:4-728:36
    Name pattern: [libsignal_core::address::{core::convert::From<u8, libsignal_core::address::DeviceId>}::from]
    Visibility: public -/
@[rust_fun
  "libsignal_core::address::{core::convert::From<u8, libsignal_core::address::DeviceId>}::from"]
axiom U8.Insts.CoreConvertFromDeviceId.from
  : libsignal_core.address.DeviceId → Result Std.U8

-- (dropped axiom libsignal_core.address.ProtocolAddress.name; provided by an imported sibling lib)

-- (dropped axiom libsignal_core.address.ProtocolAddress.device_id; provided by an imported sibling lib)

/-- [libsignal_core::address::{impl core::fmt::Display for libsignal_core::address::ProtocolAddress}::fmt]:
    Source: 'rust/core/src/address.rs', lines 824:4-824:56
    Name pattern: [libsignal_core::address::{core::fmt::Display<libsignal_core::address::ProtocolAddress>}::fmt]
    Visibility: public -/
@[rust_fun
  "libsignal_core::address::{core::fmt::Display<libsignal_core::address::ProtocolAddress>}::fmt"]
axiom libsignal_core.address.ProtocolAddress.Insts.CoreFmtDisplay.fmt
  :
  libsignal_core.address.ProtocolAddress → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [libsignal_core::curve::{impl core::clone::Clone for libsignal_core::curve::PublicKey}::clone]:
    Source: 'rust/core/src/curve.rs', lines 63:9-63:14
    Name pattern: [libsignal_core::curve::{core::clone::Clone<libsignal_core::curve::PublicKey>}::clone]
    Visibility: public -/
@[rust_fun
  "libsignal_core::curve::{core::clone::Clone<libsignal_core::curve::PublicKey>}::clone"]
axiom libsignal_core.curve.PublicKey.Insts.CoreCloneClone.clone
  : libsignal_core.curve.PublicKey → Result libsignal_core.curve.PublicKey

-- (dropped axiom libsignal_core.curve.PublicKey.deserialize; provided by an imported sibling lib)

-- (dropped axiom libsignal_core.curve.PublicKey.public_key_bytes; provided by an imported sibling lib)

-- (dropped axiom libsignal_core.curve.PublicKey.serialize; provided by an imported sibling lib)

/-- [libsignal_core::curve::{libsignal_core::curve::PublicKey}::verify_signature_for_multipart_message]:
    Source: 'rust/core/src/curve.rs', lines 138:4-142:13
    Name pattern: [libsignal_core::curve::{libsignal_core::curve::PublicKey}::verify_signature_for_multipart_message]
    Visibility: public -/
@[rust_fun
  "libsignal_core::curve::{libsignal_core::curve::PublicKey}::verify_signature_for_multipart_message"]
axiom libsignal_core.curve.PublicKey.verify_signature_for_multipart_message
  :
  libsignal_core.curve.PublicKey → Slice (Slice Std.U8) → Slice Std.U8 →
    Result Bool

-- (dropped axiom libsignal_core.curve.PublicKey.is_canonical; provided by an imported sibling lib)

/-- [libsignal_core::curve::{impl core::convert::TryFrom<&'_0 [u8], libsignal_core::curve::CurveError> for libsignal_core::curve::PublicKey}::try_from]:
    Source: 'rust/core/src/curve.rs', lines 196:4-196:57
    Name pattern: [libsignal_core::curve::{core::convert::TryFrom<libsignal_core::curve::PublicKey, &'0 [u8], libsignal_core::curve::CurveError>}::try_from]
    Visibility: public -/
@[rust_fun
  "libsignal_core::curve::{core::convert::TryFrom<libsignal_core::curve::PublicKey, &'0 [u8], libsignal_core::curve::CurveError>}::try_from"]
axiom
  libsignal_core.curve.PublicKey.Insts.CoreConvertTryFromShared0SliceU8CurveError.try_from
  :
  Slice Std.U8 → Result (core.result.Result libsignal_core.curve.PublicKey
    libsignal_core.curve.CurveError)

/-- [libsignal_core::curve::{impl core::cmp::PartialEq<libsignal_core::curve::PublicKey> for libsignal_core::curve::PublicKey}::eq]:
    Source: 'rust/core/src/curve.rs', lines 215:4-215:43
    Name pattern: [libsignal_core::curve::{core::cmp::PartialEq<libsignal_core::curve::PublicKey, libsignal_core::curve::PublicKey>}::eq]
    Visibility: public -/
@[rust_fun
  "libsignal_core::curve::{core::cmp::PartialEq<libsignal_core::curve::PublicKey, libsignal_core::curve::PublicKey>}::eq"]
axiom libsignal_core.curve.PublicKey.Insts.CoreCmpPartialEqPublicKey.eq
  :
  libsignal_core.curve.PublicKey → libsignal_core.curve.PublicKey → Result
    Bool

-- (dropped axiom libsignal_core.curve.PrivateKey.deserialize; provided by an imported sibling lib)

-- (dropped axiom libsignal_core.curve.PrivateKey.serialize; provided by an imported sibling lib)

/-- [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::public_key]:
    Source: 'rust/core/src/curve.rs', lines 259:4-259:61
    Name pattern: [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::public_key]
    Visibility: public -/
@[rust_fun
  "libsignal_core::curve::{libsignal_core::curve::PrivateKey}::public_key"]
axiom libsignal_core.curve.PrivateKey.public_key
  :
  libsignal_core.curve.PrivateKey → Result (core.result.Result
    libsignal_core.curve.PublicKey libsignal_core.curve.CurveError)

/-- [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::calculate_signature]:
    Source: 'rust/core/src/curve.rs', lines 275:4-279:38
    Name pattern: [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::calculate_signature]
    Visibility: public -/
@[rust_fun
  "libsignal_core::curve::{libsignal_core::curve::PrivateKey}::calculate_signature"]
axiom libsignal_core.curve.PrivateKey.calculate_signature
  {R : Type} (rand_core_1CryptoRngInst : rand_core_1.CryptoRng R)
  (rand_1rngRngInst : rand_1.rng.Rng R) :
  libsignal_core.curve.PrivateKey → Slice Std.U8 → R → Result
    ((core.result.Result (Slice Std.U8) libsignal_core.curve.CurveError) × R)

/-- [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::calculate_signature_for_multipart_message]:
    Source: 'rust/core/src/curve.rs', lines 283:4-287:38
    Name pattern: [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::calculate_signature_for_multipart_message]
    Visibility: public -/
@[rust_fun
  "libsignal_core::curve::{libsignal_core::curve::PrivateKey}::calculate_signature_for_multipart_message"]
axiom libsignal_core.curve.PrivateKey.calculate_signature_for_multipart_message
  {R : Type} (rand_core_1CryptoRngInst : rand_core_1.CryptoRng R)
  (rand_1rngRngInst : rand_1.rng.Rng R) :
  libsignal_core.curve.PrivateKey → Slice (Slice Std.U8) → R → Result
    ((core.result.Result (Slice Std.U8) libsignal_core.curve.CurveError) × R)

-- (dropped axiom libsignal_core.curve.PrivateKey.calculate_agreement; provided by an imported sibling lib)

/-- [libsignal_core::curve::{impl core::clone::Clone for libsignal_core::curve::KeyPair}::clone]:
    Source: 'rust/core/src/curve.rs', lines 320:15-320:20
    Name pattern: [libsignal_core::curve::{core::clone::Clone<libsignal_core::curve::KeyPair>}::clone]
    Visibility: public -/
@[rust_fun
  "libsignal_core::curve::{core::clone::Clone<libsignal_core::curve::KeyPair>}::clone"]
axiom libsignal_core.curve.KeyPair.Insts.CoreCloneClone.clone
  : libsignal_core.curve.KeyPair → Result libsignal_core.curve.KeyPair

/-- [libsignal_core::curve::{libsignal_core::curve::KeyPair}::generate]:
    Source: 'rust/core/src/curve.rs', lines 327:4-327:72
    Name pattern: [libsignal_core::curve::{libsignal_core::curve::KeyPair}::generate]
    Visibility: public -/
@[rust_fun "libsignal_core::curve::{libsignal_core::curve::KeyPair}::generate"]
axiom libsignal_core.curve.KeyPair.generate
  {R : Type} (rand_1rngRngInst : rand_1.rng.Rng R) (rand_core_1CryptoRngInst :
  rand_core_1.CryptoRng R) :
  R → Result (libsignal_core.curve.KeyPair × R)

/-- [libsignal_core::curve::{libsignal_core::curve::KeyPair}::new]:
    Source: 'rust/core/src/curve.rs', lines 343:4-343:70
    Name pattern: [libsignal_core::curve::{libsignal_core::curve::KeyPair}::new]
    Visibility: public -/
@[rust_fun "libsignal_core::curve::{libsignal_core::curve::KeyPair}::new"]
axiom libsignal_core.curve.KeyPair.new
  :
  libsignal_core.curve.PublicKey → libsignal_core.curve.PrivateKey → Result
    libsignal_core.curve.KeyPair

-- (dropped axiom libsignal_core.curve.KeyPair.from_public_and_private; provided by an imported sibling lib)

/-- [prost::error::{impl core::fmt::Debug for prost::error::EncodeError}::fmt]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/prost-0.14.4/src/error.rs', lines 184:22-184:27
    Name pattern: [prost::error::{core::fmt::Debug<prost::error::EncodeError>}::fmt]
    Visibility: public -/
@[rust_fun "prost::error::{core::fmt::Debug<prost::error::EncodeError>}::fmt"]
axiom prost.error.EncodeError.Insts.CoreFmtDebug.fmt
  :
  prost.error.EncodeError → core.fmt.Formatter → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [prost::message::Message::encode]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/prost-0.14.4/src/message.rs', lines 46:4-48:20
    Name pattern: [prost::message::Message::encode]
    Visibility: public -/
-- Opaque default indexed by the types instead of the instance. Rust coherence
-- allows at most one impl of a trait per type, so this is as general as one
-- external per impl, and `impl_def` can close the instance.
axiom prost.message.Message.encode.external
  {Self : Type} {T1 : Type} :
  Self → T1 → Result ((core.result.Result Unit prost.error.EncodeError) ×
    T1)

@[trait_default, rust_fun "prost::message::Message::encode"]
noncomputable def prost.message.Message.encode.default
  {Self : Type} {T1 : Type} (MessageInst : prost.message.Message Self)
  (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T1) :
  Self → T1 → Result ((core.result.Result Unit prost.error.EncodeError) ×
    T1) :=
  prost.message.Message.encode.external

/-- [prost::message::Message::encode_to_vec]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/prost-0.14.4/src/message.rs', lines 61:4-63:20
    Name pattern: [prost::message::Message::encode_to_vec]
    Visibility: public -/
-- Opaque default indexed by the types instead of the instance. Rust coherence
-- allows at most one impl of a trait per type, so this is as general as one
-- external per impl, and `impl_def` can close the instance.
axiom prost.message.Message.encode_to_vec.external
  {Self : Type} : Self → Result (alloc.vec.Vec Std.U8)

@[trait_default, rust_fun "prost::message::Message::encode_to_vec"]
noncomputable def prost.message.Message.encode_to_vec.default
  {Self : Type} (MessageInst : prost.message.Message Self) :
  Self → Result (alloc.vec.Vec Std.U8) :=
  prost.message.Message.encode_to_vec.external

/-- [prost::message::Message::decode]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/prost-0.14.4/src/message.rs', lines 105:4-107:22
    Name pattern: [prost::message::Message::decode]
    Visibility: public -/
-- Opaque default indexed by the types instead of the instance. Rust coherence
-- allows at most one impl of a trait per type, so this is as general as one
-- external per impl, and `impl_def` can close the instance.
axiom prost.message.Message.decode.external
  {Self : Type} {T1 : Type} :
  T1 → Result (core.result.Result Self prost.error.DecodeError)

@[trait_default, rust_fun "prost::message::Message::decode"]
noncomputable def prost.message.Message.decode.default
  {Self : Type} {T1 : Type} (MessageInst : prost.message.Message Self)
  (coredefaultDefaultInst : core.default.Default Self) (bytesbufbuf_implBufInst
  : bytes.buf.buf_impl.Buf T1) :
  T1 → Result (core.result.Result Self prost.error.DecodeError) :=
  prost.message.Message.decode.external

/-- [rand_core#1::TryRngCore::unwrap_err]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.5/src/lib.rs', lines 232:4-234:20
    Name pattern: [rand_core#1::TryRngCore::unwrap_err]
    Visibility: public -/
-- rand_core 0.9.5 returns `UnwrapErr(self)`; Aeneas models `UnwrapErr<R>` as `R`.
@[trait_default, rust_fun "rand_core#1::TryRngCore::unwrap_err"]
def rand_core_1.TryRngCore.unwrap_err.default
  {Self : Type} {Clause0_Error : Type} (TryRngCoreInst : rand_core_1.TryRngCore
  Self Clause0_Error) :
  Self → Result (rand_core_1.UnwrapErr Self Clause0_Error) :=
  fun self => ok self

/-- [rand_core#1::{impl rand_core#1::RngCore for rand_core#1::UnwrapErr<R, Clause0_Error>}::fill_bytes]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.5/src/lib.rs', lines 312:4-312:44
    Name pattern: [rand_core#1::{rand_core#1::RngCore<rand_core#1::UnwrapErr<@R, @Clause0_Error>>}::fill_bytes]
    Visibility: public -/
@[rust_fun
  "rand_core#1::{rand_core#1::RngCore<rand_core#1::UnwrapErr<@R, @Clause0_Error>>}::fill_bytes"]
axiom rand_core_1.UnwrapErr.Insts.Rand_core_1RngCore.fill_bytes
  {R : Type} {Clause0_Error : Type} (TryRngCoreInst : rand_core_1.TryRngCore R
  Clause0_Error) :
  rand_core_1.UnwrapErr R Clause0_Error → Slice Std.U8 → Result
    ((rand_core_1.UnwrapErr R Clause0_Error) × (Slice Std.U8))

/-- [rand_core#1::{impl rand_core#1::RngCore for rand_core#1::UnwrapErr<R, Clause0_Error>}::next_u64]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.5/src/lib.rs', lines 307:4-307:33
    Name pattern: [rand_core#1::{rand_core#1::RngCore<rand_core#1::UnwrapErr<@R, @Clause0_Error>>}::next_u64]
    Visibility: public -/
@[rust_fun
  "rand_core#1::{rand_core#1::RngCore<rand_core#1::UnwrapErr<@R, @Clause0_Error>>}::next_u64"]
axiom rand_core_1.UnwrapErr.Insts.Rand_core_1RngCore.next_u64
  {R : Type} {Clause0_Error : Type} (TryRngCoreInst : rand_core_1.TryRngCore R
  Clause0_Error) :
  rand_core_1.UnwrapErr R Clause0_Error → Result (Std.U64 ×
    (rand_core_1.UnwrapErr R Clause0_Error))

/-- [rand_core#1::{impl rand_core#1::RngCore for rand_core#1::UnwrapErr<R, Clause0_Error>}::next_u32]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.5/src/lib.rs', lines 302:4-302:33
    Name pattern: [rand_core#1::{rand_core#1::RngCore<rand_core#1::UnwrapErr<@R, @Clause0_Error>>}::next_u32]
    Visibility: public -/
@[rust_fun
  "rand_core#1::{rand_core#1::RngCore<rand_core#1::UnwrapErr<@R, @Clause0_Error>>}::next_u32"]
axiom rand_core_1.UnwrapErr.Insts.Rand_core_1RngCore.next_u32
  {R : Type} {Clause0_Error : Type} (TryRngCoreInst : rand_core_1.TryRngCore R
  Clause0_Error) :
  rand_core_1.UnwrapErr R Clause0_Error → Result (Std.U32 ×
    (rand_core_1.UnwrapErr R Clause0_Error))

/-- [rand_core#1::os::{impl core::fmt::Debug for rand_core#1::os::OsError}::fmt]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.5/src/os.rs', lines 50:22-50:27
    Name pattern: [rand_core#1::os::{core::fmt::Debug<rand_core#1::os::OsError>}::fmt]
    Visibility: public -/
@[rust_fun
  "rand_core#1::os::{core::fmt::Debug<rand_core#1::os::OsError>}::fmt"]
axiom rand_core_1.os.OsError.Insts.CoreFmtDebug.fmt
  :
  rand_core_1.os.OsError → core.fmt.Formatter → Result ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [rand_core#1::os::{impl core::fmt::Display for rand_core#1::os::OsError}::fmt]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.5/src/os.rs', lines 55:4-55:72
    Name pattern: [rand_core#1::os::{core::fmt::Display<rand_core#1::os::OsError>}::fmt]
    Visibility: public -/
@[rust_fun
  "rand_core#1::os::{core::fmt::Display<rand_core#1::os::OsError>}::fmt"]
axiom rand_core_1.os.OsError.Insts.CoreFmtDisplay.fmt
  :
  rand_core_1.os.OsError → core.fmt.Formatter → Result ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [rand_core#1::os::{impl rand_core#1::TryRngCore<rand_core#1::os::OsError> for rand_core#1::os::OsRng}::try_fill_bytes]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.5/src/os.rs', lines 97:4-97:76
    Name pattern: [rand_core#1::os::{rand_core#1::TryRngCore<rand_core#1::os::OsRng, rand_core#1::os::OsError>}::try_fill_bytes]
    Visibility: public -/
@[rust_fun
  "rand_core#1::os::{rand_core#1::TryRngCore<rand_core#1::os::OsRng, rand_core#1::os::OsError>}::try_fill_bytes"]
axiom rand_core_1.os.OsRng.Insts.Rand_core_1TryRngCoreOsError.try_fill_bytes
  :
  rand_core_1.os.OsRng → Slice Std.U8 → Result ((core.result.Result Unit
    rand_core_1.os.OsError) × rand_core_1.os.OsRng × (Slice Std.U8))

/-- [rand_core#1::os::{impl rand_core#1::TryRngCore<rand_core#1::os::OsError> for rand_core#1::os::OsRng}::try_next_u64]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.5/src/os.rs', lines 92:4-92:58
    Name pattern: [rand_core#1::os::{rand_core#1::TryRngCore<rand_core#1::os::OsRng, rand_core#1::os::OsError>}::try_next_u64]
    Visibility: public -/
@[rust_fun
  "rand_core#1::os::{rand_core#1::TryRngCore<rand_core#1::os::OsRng, rand_core#1::os::OsError>}::try_next_u64"]
axiom rand_core_1.os.OsRng.Insts.Rand_core_1TryRngCoreOsError.try_next_u64
  :
  rand_core_1.os.OsRng → Result ((core.result.Result Std.U64
    rand_core_1.os.OsError) × rand_core_1.os.OsRng)

/-- [rand_core#1::os::{impl rand_core#1::TryRngCore<rand_core#1::os::OsError> for rand_core#1::os::OsRng}::try_next_u32]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.5/src/os.rs', lines 87:4-87:58
    Name pattern: [rand_core#1::os::{rand_core#1::TryRngCore<rand_core#1::os::OsRng, rand_core#1::os::OsError>}::try_next_u32]
    Visibility: public -/
@[rust_fun
  "rand_core#1::os::{rand_core#1::TryRngCore<rand_core#1::os::OsRng, rand_core#1::os::OsError>}::try_next_u32"]
axiom rand_core_1.os.OsRng.Insts.Rand_core_1TryRngCoreOsError.try_next_u32
  :
  rand_core_1.os.OsRng → Result ((core.result.Result Std.U32
    rand_core_1.os.OsError) × rand_core_1.os.OsRng)

/-- [signal_crypto::aes_cbc::aes_256_cbc_encrypt]:
    Source: 'rust/crypto/src/aes_cbc.rs', lines 26:0-30:37
    Name pattern: [signal_crypto::aes_cbc::aes_256_cbc_encrypt]
    Visibility: public -/
@[rust_fun "signal_crypto::aes_cbc::aes_256_cbc_encrypt"]
-- Alias of the crypto-cbc profile's external.
noncomputable abbrev signal_crypto.aes_cbc.aes_256_cbc_encrypt :=
  _root_.aes_cbc.aes_256_cbc_encrypt

/-- [signal_crypto::aes_cbc::aes_256_cbc_decrypt]:
    Source: 'rust/crypto/src/aes_cbc.rs', lines 37:0-41:37
    Name pattern: [signal_crypto::aes_cbc::aes_256_cbc_decrypt]
    Visibility: public -/
@[rust_fun "signal_crypto::aes_cbc::aes_256_cbc_decrypt"]
-- Alias of the crypto-cbc profile's external.
noncomputable abbrev signal_crypto.aes_cbc.aes_256_cbc_decrypt :=
  _root_.aes_cbc.aes_256_cbc_decrypt

/-- [spqr::chain::{impl core::default::Default for spqr::chain::ChainParams}::default]:
    Source: '/cargo/git/checkouts/sparsepostquantumratchet-b58d7f56e3645ccd/06959b4/src/chain.rs', lines 29:4-29:24
    Name pattern: [spqr::chain::{core::default::Default<spqr::chain::ChainParams>}::default]
    Visibility: public -/
@[rust_fun
  "spqr::chain::{core::default::Default<spqr::chain::ChainParams>}::default"]
axiom spqr.chain.ChainParams.Insts.CoreDefaultDefault.default
  : Result spqr.chain.ChainParams

/-- [spqr::{impl core::fmt::Display for spqr::Error}::fmt]:
    Source: '/cargo/git/checkouts/sparsepostquantumratchet-b58d7f56e3645ccd/06959b4/src/lib.rs', lines 96:16-96:32
    Name pattern: [spqr::{core::fmt::Display<spqr::Error>}::fmt]
    Visibility: public -/
@[rust_fun "spqr::{core::fmt::Display<spqr::Error>}::fmt"]
axiom spqr.Error.Insts.CoreFmtDisplay.fmt
  :
  spqr.Error → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

-- SPQR v1.6.0 interface consumed by libsignal (`initial_state`, `send`, `recv`).
-- SPQR-verify extracts and verifies SPQR itself.
/-- [spqr::initial_state]:
    Source: '/cargo/git/checkouts/sparsepostquantumratchet-b58d7f56e3645ccd/06959b4/src/lib.rs', lines 211:0-211:70
    Name pattern: [spqr::initial_state]
    Visibility: public -/
@[rust_fun "spqr::initial_state"]
axiom spqr.initial_state
  :
  spqr.Params → Result (core.result.Result (alloc.vec.Vec Std.U8) spqr.Error)

/-- [spqr::send]:
    Source: '/cargo/git/checkouts/sparsepostquantumratchet-b58d7f56e3645ccd/06959b4/src/lib.rs', lines 264:0-264:92
    Name pattern: [spqr::send]
    Visibility: public -/
@[rust_fun "spqr::send"]
axiom spqr.send
  {R : Type} (rand_1rngRngInst : rand_1.rng.Rng R) (rand_core_1CryptoRngInst :
  rand_core_1.CryptoRng R) :
  alloc.vec.Vec Std.U8 → R → Result ((core.result.Result spqr.Send
    spqr.Error) × R)

/-- [spqr::recv]:
    Source: '/cargo/git/checkouts/sparsepostquantumratchet-b58d7f56e3645ccd/06959b4/src/lib.rs', lines 355:0-355:84
    Name pattern: [spqr::recv]
    Visibility: public -/
@[rust_fun "spqr::recv"]
axiom spqr.recv
  :
  alloc.vec.Vec Std.U8 → alloc.vec.Vec Std.U8 → Result (core.result.Result
    spqr.Recv spqr.Error)

/-- [subtle::{impl core::convert::From<subtle::Choice> for bool}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 153:4-153:35
    Name pattern: [subtle::{core::convert::From<bool, subtle::Choice>}::from]
    Visibility: public -/
-- Transcribes `source.0 != 0`; the `debug_assert!` is not modelled.
@[rust_fun "subtle::{core::convert::From<bool, subtle::Choice>}::from"]
def Bool.Insts.CoreConvertFromChoice.from (source : subtle.Choice) : Result Bool :=
  ok (source.val != 0#u8)

/-- [subtle::{impl subtle::ConstantTimeEq for [T]}::ct_eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 313:4-313:41
    Name pattern: [subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq]
    Visibility: public -/
-- Transcribes the loop in `subtle`: 0 when the lengths differ, otherwise the
-- bitwise AND of the elementwise results, starting from 1.
@[rust_fun "subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq"]
def Slice.Insts.SubtleConstantTimeEq.ct_eq
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T) (s rhs : Slice T) :
  Result subtle.Choice :=
  if s.length ≠ rhs.length then ok ⟨0#u8⟩
  else do
    let x ← (List.zip s.val rhs.val).foldlM
      (fun (x : Std.U8) (p : T × T) => do
        let c ← ConstantTimeEqInst.ct_eq p.1 p.2
        ok (x &&& c.val))
      1#u8
    ok ⟨x⟩

/-- [subtle::{impl subtle::ConstantTimeEq for u8}::ct_eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 348:12-348:51
    Name pattern: [subtle::{subtle::ConstantTimeEq<u8>}::ct_eq]
    Visibility: public -/
-- The value computed by the branch-free comparison in `subtle`: 1 when the
-- bytes are equal, 0 otherwise. Timing is not modelled.
@[rust_fun "subtle::{subtle::ConstantTimeEq<u8>}::ct_eq"]
def U8.Insts.SubtleConstantTimeEq.ct_eq (a b : Std.U8) : Result subtle.Choice :=
  ok ⟨if a = b then 1#u8 else 0#u8⟩

/-- [uuid::{impl core::clone::Clone for uuid::Uuid}::clone]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/uuid-1.23.4/src/lib.rs', lines 446:9-446:14
    Name pattern: [uuid::{core::clone::Clone<uuid::Uuid>}::clone]
    Visibility: public -/
@[rust_fun "uuid::{core::clone::Clone<uuid::Uuid>}::clone"]
axiom uuid.Uuid.Insts.CoreCloneClone.clone : uuid.Uuid → Result uuid.Uuid

-- (dropped axiom uuid.Uuid.as_bytes; provided by an imported sibling lib)

/-- [libsignal_protocol::proto::fingerprint::{impl prost::message::Message for libsignal_protocol::proto::fingerprint::CombinedFingerprints}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.fingerprint.rs', lines 8:37-8:53
    Visibility: public -/
axiom proto.fingerprint.CombinedFingerprints.Insts.ProstMessageMessage.clear
  :
  proto.fingerprint.CombinedFingerprints → Result
    proto.fingerprint.CombinedFingerprints

/-- [libsignal_protocol::proto::fingerprint::{impl prost::message::Message for libsignal_protocol::proto::fingerprint::CombinedFingerprints}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.fingerprint.rs', lines 8:37-8:53
    Visibility: public -/
axiom
  proto.fingerprint.CombinedFingerprints.Insts.ProstMessageMessage.encoded_len
  : proto.fingerprint.CombinedFingerprints → Result Std.Usize

/-- [libsignal_protocol::proto::fingerprint::{impl prost::message::Message for libsignal_protocol::proto::fingerprint::CombinedFingerprints}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.fingerprint.rs', lines 8:37-8:53
    Visibility: public -/
axiom
  proto.fingerprint.CombinedFingerprints.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.fingerprint.CombinedFingerprints → Std.U32 →
    prost.encoding.wire_type.WireType → T0 → prost.encoding.DecodeContext
    → Result ((core.result.Result Unit prost.error.DecodeError) ×
    proto.fingerprint.CombinedFingerprints × T0)

/-- [libsignal_protocol::proto::fingerprint::{impl prost::message::Message for libsignal_protocol::proto::fingerprint::CombinedFingerprints}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.fingerprint.rs', lines 8:37-8:53
    Visibility: public -/
axiom
  proto.fingerprint.CombinedFingerprints.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.fingerprint.CombinedFingerprints → T0 → Result T0

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SessionStructure}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 2:27-2:43
    Visibility: public -/
axiom proto.storage.SessionStructure.Insts.ProstMessageMessage.clear
  : proto.storage.SessionStructure → Result proto.storage.SessionStructure

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SessionStructure}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 2:27-2:43
    Visibility: public -/
axiom proto.storage.SessionStructure.Insts.ProstMessageMessage.encoded_len
  : proto.storage.SessionStructure → Result Std.Usize

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SessionStructure}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 2:27-2:43
    Visibility: public -/
axiom proto.storage.SessionStructure.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.storage.SessionStructure → Std.U32 →
    prost.encoding.wire_type.WireType → T0 → prost.encoding.DecodeContext
    → Result ((core.result.Result Unit prost.error.DecodeError) ×
    proto.storage.SessionStructure × T0)

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SessionStructure}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 2:27-2:43
    Visibility: public -/
axiom proto.storage.SessionStructure.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.storage.SessionStructure → T0 → Result T0

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::RecordStructure}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 92:27-92:43
    Visibility: public -/
axiom proto.storage.RecordStructure.Insts.ProstMessageMessage.clear
  : proto.storage.RecordStructure → Result proto.storage.RecordStructure

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::RecordStructure}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 92:27-92:43
    Visibility: public -/
axiom proto.storage.RecordStructure.Insts.ProstMessageMessage.encoded_len
  : proto.storage.RecordStructure → Result Std.Usize

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::RecordStructure}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 92:27-92:43
    Visibility: public -/
axiom proto.storage.RecordStructure.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.storage.RecordStructure → Std.U32 →
    prost.encoding.wire_type.WireType → T0 → prost.encoding.DecodeContext
    → Result ((core.result.Result Unit prost.error.DecodeError) ×
    proto.storage.RecordStructure × T0)

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::RecordStructure}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 92:27-92:43
    Visibility: public -/
axiom proto.storage.RecordStructure.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.storage.RecordStructure → T0 → Result T0

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::PreKeyRecordStructure}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 100:37-100:53
    Visibility: public -/
axiom proto.storage.PreKeyRecordStructure.Insts.ProstMessageMessage.clear
  :
  proto.storage.PreKeyRecordStructure → Result
    proto.storage.PreKeyRecordStructure

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::PreKeyRecordStructure}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 100:37-100:53
    Visibility: public -/
axiom proto.storage.PreKeyRecordStructure.Insts.ProstMessageMessage.encoded_len
  : proto.storage.PreKeyRecordStructure → Result Std.Usize

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::PreKeyRecordStructure}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 100:37-100:53
    Visibility: public -/
axiom proto.storage.PreKeyRecordStructure.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.storage.PreKeyRecordStructure → Std.U32 →
    prost.encoding.wire_type.WireType → T0 → prost.encoding.DecodeContext
    → Result ((core.result.Result Unit prost.error.DecodeError) ×
    proto.storage.PreKeyRecordStructure × T0)

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::PreKeyRecordStructure}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 100:37-100:53
    Visibility: public -/
axiom proto.storage.PreKeyRecordStructure.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.storage.PreKeyRecordStructure → T0 → Result T0

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SignedPreKeyRecordStructure}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 109:37-109:53
    Visibility: public -/
axiom proto.storage.SignedPreKeyRecordStructure.Insts.ProstMessageMessage.clear
  :
  proto.storage.SignedPreKeyRecordStructure → Result
    proto.storage.SignedPreKeyRecordStructure

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SignedPreKeyRecordStructure}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 109:37-109:53
    Visibility: public -/
axiom
  proto.storage.SignedPreKeyRecordStructure.Insts.ProstMessageMessage.encoded_len
  : proto.storage.SignedPreKeyRecordStructure → Result Std.Usize

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SignedPreKeyRecordStructure}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 109:37-109:53
    Visibility: public -/
axiom
  proto.storage.SignedPreKeyRecordStructure.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.storage.SignedPreKeyRecordStructure → Std.U32 →
    prost.encoding.wire_type.WireType → T0 → prost.encoding.DecodeContext
    → Result ((core.result.Result Unit prost.error.DecodeError) ×
    proto.storage.SignedPreKeyRecordStructure × T0)

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SignedPreKeyRecordStructure}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 109:37-109:53
    Visibility: public -/
axiom
  proto.storage.SignedPreKeyRecordStructure.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.storage.SignedPreKeyRecordStructure → T0 → Result T0

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::IdentityKeyPairStructure}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 122:37-122:53
    Visibility: public -/
axiom proto.storage.IdentityKeyPairStructure.Insts.ProstMessageMessage.clear
  :
  proto.storage.IdentityKeyPairStructure → Result
    proto.storage.IdentityKeyPairStructure

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::IdentityKeyPairStructure}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 122:37-122:53
    Visibility: public -/
axiom
  proto.storage.IdentityKeyPairStructure.Insts.ProstMessageMessage.encoded_len
  : proto.storage.IdentityKeyPairStructure → Result Std.Usize

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::IdentityKeyPairStructure}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 122:37-122:53
    Visibility: public -/
axiom
  proto.storage.IdentityKeyPairStructure.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.storage.IdentityKeyPairStructure → Std.U32 →
    prost.encoding.wire_type.WireType → T0 → prost.encoding.DecodeContext
    → Result ((core.result.Result Unit prost.error.DecodeError) ×
    proto.storage.IdentityKeyPairStructure × T0)

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::IdentityKeyPairStructure}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 122:37-122:53
    Visibility: public -/
axiom
  proto.storage.IdentityKeyPairStructure.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.storage.IdentityKeyPairStructure → T0 → Result T0

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SenderKeyRecordStructure}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 172:27-172:43
    Visibility: public -/
axiom proto.storage.SenderKeyRecordStructure.Insts.ProstMessageMessage.clear
  :
  proto.storage.SenderKeyRecordStructure → Result
    proto.storage.SenderKeyRecordStructure

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SenderKeyRecordStructure}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 172:27-172:43
    Visibility: public -/
axiom
  proto.storage.SenderKeyRecordStructure.Insts.ProstMessageMessage.encoded_len
  : proto.storage.SenderKeyRecordStructure → Result Std.Usize

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SenderKeyRecordStructure}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 172:27-172:43
    Visibility: public -/
axiom
  proto.storage.SenderKeyRecordStructure.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.storage.SenderKeyRecordStructure → Std.U32 →
    prost.encoding.wire_type.WireType → T0 → prost.encoding.DecodeContext
    → Result ((core.result.Result Unit prost.error.DecodeError) ×
    proto.storage.SenderKeyRecordStructure × T0)

/-- [libsignal_protocol::proto::storage::{impl prost::message::Message for libsignal_protocol::proto::storage::SenderKeyRecordStructure}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.storage.rs', lines 172:27-172:43
    Visibility: public -/
axiom
  proto.storage.SenderKeyRecordStructure.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.storage.SenderKeyRecordStructure → T0 → Result T0

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SignalMessage}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 2:37-2:53
    Visibility: public -/
axiom proto.wire.SignalMessage.Insts.ProstMessageMessage.clear
  : proto.wire.SignalMessage → Result proto.wire.SignalMessage

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SignalMessage}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 2:37-2:53
    Visibility: public -/
axiom proto.wire.SignalMessage.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.wire.SignalMessage → Std.U32 → prost.encoding.wire_type.WireType
    → T0 → prost.encoding.DecodeContext → Result ((core.result.Result
    Unit prost.error.DecodeError) × proto.wire.SignalMessage × T0)

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SignalMessage}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 2:37-2:53
    Visibility: public -/
axiom proto.wire.SignalMessage.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.wire.SignalMessage → T0 → Result T0

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SignalMessage}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 2:37-2:53
    Visibility: public -/
axiom proto.wire.SignalMessage.Insts.ProstMessageMessage.encoded_len
  : proto.wire.SignalMessage → Result Std.Usize

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::PreKeySignalMessage}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 17:37-17:53
    Visibility: public -/
axiom proto.wire.PreKeySignalMessage.Insts.ProstMessageMessage.clear
  : proto.wire.PreKeySignalMessage → Result proto.wire.PreKeySignalMessage

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::PreKeySignalMessage}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 17:37-17:53
    Visibility: public -/
axiom proto.wire.PreKeySignalMessage.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.wire.PreKeySignalMessage → Std.U32 →
    prost.encoding.wire_type.WireType → T0 → prost.encoding.DecodeContext
    → Result ((core.result.Result Unit prost.error.DecodeError) ×
    proto.wire.PreKeySignalMessage × T0)

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::PreKeySignalMessage}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 17:37-17:53
    Visibility: public -/
axiom proto.wire.PreKeySignalMessage.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.wire.PreKeySignalMessage → T0 → Result T0

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::PreKeySignalMessage}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 17:37-17:53
    Visibility: public -/
axiom proto.wire.PreKeySignalMessage.Insts.ProstMessageMessage.encoded_len
  : proto.wire.PreKeySignalMessage → Result Std.Usize

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SenderKeyMessage}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 37:37-37:53
    Visibility: public -/
axiom proto.wire.SenderKeyMessage.Insts.ProstMessageMessage.clear
  : proto.wire.SenderKeyMessage → Result proto.wire.SenderKeyMessage

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SenderKeyMessage}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 37:37-37:53
    Visibility: public -/
axiom proto.wire.SenderKeyMessage.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.wire.SenderKeyMessage → Std.U32 → prost.encoding.wire_type.WireType
    → T0 → prost.encoding.DecodeContext → Result ((core.result.Result
    Unit prost.error.DecodeError) × proto.wire.SenderKeyMessage × T0)

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SenderKeyMessage}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 37:37-37:53
    Visibility: public -/
axiom proto.wire.SenderKeyMessage.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.wire.SenderKeyMessage → T0 → Result T0

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SenderKeyMessage}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 37:37-37:53
    Visibility: public -/
axiom proto.wire.SenderKeyMessage.Insts.ProstMessageMessage.encoded_len
  : proto.wire.SenderKeyMessage → Result Std.Usize

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SenderKeyDistributionMessage}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 48:37-48:53
    Visibility: public -/
axiom proto.wire.SenderKeyDistributionMessage.Insts.ProstMessageMessage.clear
  :
  proto.wire.SenderKeyDistributionMessage → Result
    proto.wire.SenderKeyDistributionMessage

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SenderKeyDistributionMessage}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 48:37-48:53
    Visibility: public -/
axiom
  proto.wire.SenderKeyDistributionMessage.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.wire.SenderKeyDistributionMessage → Std.U32 →
    prost.encoding.wire_type.WireType → T0 → prost.encoding.DecodeContext
    → Result ((core.result.Result Unit prost.error.DecodeError) ×
    proto.wire.SenderKeyDistributionMessage × T0)

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SenderKeyDistributionMessage}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 48:37-48:53
    Visibility: public -/
axiom
  proto.wire.SenderKeyDistributionMessage.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.wire.SenderKeyDistributionMessage → T0 → Result T0

/-- [libsignal_protocol::proto::wire::{impl prost::message::Message for libsignal_protocol::proto::wire::SenderKeyDistributionMessage}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signal.proto.wire.rs', lines 48:37-48:53
    Visibility: public -/
axiom
  proto.wire.SenderKeyDistributionMessage.Insts.ProstMessageMessage.encoded_len
  : proto.wire.SenderKeyDistributionMessage → Result Std.Usize

/-- [libsignal_protocol::proto::service::{impl prost::message::Message for libsignal_protocol::proto::service::DecryptionErrorMessage}::clear]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signalservice.rs', lines 23:37-23:53
    Visibility: public -/
axiom proto.service.DecryptionErrorMessage.Insts.ProstMessageMessage.clear
  :
  proto.service.DecryptionErrorMessage → Result
    proto.service.DecryptionErrorMessage

/-- [libsignal_protocol::proto::service::{impl prost::message::Message for libsignal_protocol::proto::service::DecryptionErrorMessage}::encoded_len]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signalservice.rs', lines 23:37-23:53
    Visibility: public -/
axiom
  proto.service.DecryptionErrorMessage.Insts.ProstMessageMessage.encoded_len
  : proto.service.DecryptionErrorMessage → Result Std.Usize

/-- [libsignal_protocol::proto::service::{impl prost::message::Message for libsignal_protocol::proto::service::DecryptionErrorMessage}::merge_field]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signalservice.rs', lines 23:37-23:53
    Visibility: public -/
axiom
  proto.service.DecryptionErrorMessage.Insts.ProstMessageMessage.merge_field
  {T0 : Type} (bytesbufbuf_implBufInst : bytes.buf.buf_impl.Buf T0) :
  proto.service.DecryptionErrorMessage → Std.U32 →
    prost.encoding.wire_type.WireType → T0 → prost.encoding.DecodeContext
    → Result ((core.result.Result Unit prost.error.DecodeError) ×
    proto.service.DecryptionErrorMessage × T0)

/-- [libsignal_protocol::proto::service::{impl prost::message::Message for libsignal_protocol::proto::service::DecryptionErrorMessage}::encode_raw]:
    Source: '.aeneas/cargo/0855ce1b8ed3958512b6c19de6bf3035b7acb552/darwin-arm64/aarch64-apple-darwin/debug/build/libsignal-protocol/f13d4e70addacea3/out/signalservice.rs', lines 23:37-23:53
    Visibility: public -/
axiom proto.service.DecryptionErrorMessage.Insts.ProstMessageMessage.encode_raw
  {T0 : Type} (bytesbufbuf_mutBufMutInst : bytes.buf.buf_mut.BufMut T0) :
  proto.service.DecryptionErrorMessage → T0 → Result T0

/-- [libsignal_protocol::crypto::aes_256_ctr_encrypt]:
    Source: 'rust/protocol/src/crypto.rs', lines 30:0-40:1 -/
axiom crypto.aes_256_ctr_encrypt
  :
  Slice Std.U8 → Slice Std.U8 → Result (core.result.Result (alloc.vec.Vec
    Std.U8) crypto.EncryptionError)

/-- [libsignal_protocol::crypto::hkdf_sha256]:
    Source: 'rust/protocol/src/crypto.rs', lines 50:0-57:1 -/
axiom crypto.hkdf_sha256
  :
  Option (Slice Std.U8) → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
    Result ((core.result.Result Unit hkdf.errors.InvalidLength) × (Slice
    Std.U8))

/-- [libsignal_protocol::crypto::hmac_sha256]:
    Source: 'rust/protocol/src/crypto.rs', lines 59:0-65:1 -/
axiom crypto.hmac_sha256
  : Slice Std.U8 → Slice Std.U8 → Result (Array Std.U8 32#usize)

/-- [libsignal_protocol::crypto::hmac_sha256_parts]:
    Source: 'rust/protocol/src/crypto.rs', lines 69:0-76:1 -/
axiom crypto.hmac_sha256_parts
  : Slice Std.U8 → Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)

/-- [libsignal_protocol::crypto::aes256_ctr_hmacsha256_decrypt]:
    Source: 'rust/protocol/src/crypto.rs', lines 89:0-103:1 -/
axiom crypto.aes256_ctr_hmacsha256_decrypt
  :
  Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Result (core.result.Result
    (alloc.vec.Vec Std.U8) crypto.DecryptionError)

/-- [libsignal_protocol::double_ratchet::log_duplicate_message]:
    Source: 'rust/protocol/src/double_ratchet.rs', lines 68:0-70:1 -/
-- Logging has no effect on protocol state or results.
def double_ratchet.log_duplicate_message
  (_remote_address_for_logging : Str) (_counter : Std.U32) : Result Unit :=
  ok ()

/-- [libsignal_protocol::double_ratchet::log_future_message_limit]:
    Source: 'rust/protocol/src/double_ratchet.rs', lines 72:0-82:1 -/
-- Logging has no effect on protocol state or results.
def double_ratchet.log_future_message_limit
  (_remote_address_for_logging : Str) (_max_forward_jumps : Std.Usize)
  (_chain_index _counter : Std.U32) : Result Unit :=
  ok ()

/-- [libsignal_protocol::double_ratchet::log_jump_ahead]:
    Source: 'rust/protocol/src/double_ratchet.rs', lines 84:0-88:1 -/
-- Logging has no effect on protocol state or results.
def double_ratchet.log_jump_ahead
  (_remote_address_for_logging : Str) (_jump : Std.Usize)
  (_chain_index _counter : Std.U32) : Result Unit :=
  ok ()

/-- [libsignal_protocol::double_ratchet::log_corrupt_receiver_chain]:
    Source: 'rust/protocol/src/double_ratchet.rs', lines 90:0-92:1 -/
-- Logging has no effect on protocol state or results.
def double_ratchet.log_corrupt_receiver_chain : Result Unit :=
  ok ()

/-- [libsignal_protocol::state::session::{impl core::convert::From<libsignal_protocol::state::session::InvalidSessionError> for libsignal_protocol::error::SignalProtocolError}::from]:
    Source: 'rust/protocol/src/state/session.rs', lines 36:4-38:5
    Visibility: public -/
axiom error.SignalProtocolError.Insts.CoreConvertFromInvalidSessionError.from
  : state.session.InvalidSessionError → Result error.SignalProtocolError

/-- [libsignal_protocol::ratchet::keys::{libsignal_protocol::ratchet::keys::RootKey}::create_chain]:
    Source: 'rust/protocol/src/ratchet/keys.rs', lines 203:4-221:5 -/
axiom ratchet.keys.RootKey.create_chain
  :
  ratchet.keys.RootKey → libsignal_core.curve.PublicKey →
    libsignal_core.curve.PrivateKey → Result (core.result.Result
    (ratchet.keys.RootKey × ratchet.keys.ChainKey) error.SignalProtocolError)

/-- [libsignal_protocol::fingerprint::get_encoded_string]:
    Source: 'rust/protocol/src/fingerprint.rs', lines 42:0-64:1 -/
axiom fingerprint.get_encoded_string
  : Slice Std.U8 → Result (core.result.Result String fingerprint.Error)

/-- [libsignal_protocol::fingerprint::{libsignal_protocol::fingerprint::ScannableFingerprint}::deserialize]:
    Source: 'rust/protocol/src/fingerprint.rs', lines 91:4-108:5
    Visibility: public -/
axiom fingerprint.ScannableFingerprint.deserialize
  :
  Slice Std.U8 → Result (core.result.Result fingerprint.ScannableFingerprint
    fingerprint.Error)

/-- [libsignal_protocol::fingerprint::{libsignal_protocol::fingerprint::ScannableFingerprint}::compare]:
    Source: 'rust/protocol/src/fingerprint.rs', lines 124:4-151:5
    Visibility: public -/
axiom fingerprint.ScannableFingerprint.compare
  :
  fingerprint.ScannableFingerprint → Slice Std.U8 → Result
    (core.result.Result Bool fingerprint.Error)

/-- [libsignal_protocol::fingerprint::{libsignal_protocol::fingerprint::Fingerprint}::get_fingerprint]:
    Source: 'rust/protocol/src/fingerprint.rs', lines 161:4-192:5 -/
axiom fingerprint.Fingerprint.get_fingerprint
  :
  Std.U32 → Slice Std.U8 → identity_key.IdentityKey → Result
    (core.result.Result (alloc.vec.Vec Std.U8) fingerprint.Error)

/-- [libsignal_protocol::fingerprint::{libsignal_protocol::fingerprint::Fingerprint}::display_string]:
    Source: 'rust/protocol/src/fingerprint.rs', lines 211:4-213:5
    Visibility: public -/
axiom fingerprint.Fingerprint.display_string
  :
  fingerprint.Fingerprint → Result (core.result.Result String
    fingerprint.Error)

/-- [libsignal_protocol::kem::kyber1024::{impl libsignal_protocol::kem::Parameters for libsignal_protocol::kem::kyber1024::Parameters}::encapsulate]:
    Source: 'rust/protocol/src/kem/kyber1024.rs', lines 31:4-40:5 -/
axiom
  kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate
  {R : Type} (rand_core_1CryptoRngInst : rand_core_1.CryptoRng R) :
  kem.KeyMaterial kem.Public → R → Result ((core.result.Result ((Slice
    Std.U8) × (Slice Std.U8)) kem.BadKEMKeyLength) × R)

/-- [libsignal_protocol::kem::kyber1024::{impl libsignal_protocol::kem::Parameters for libsignal_protocol::kem::kyber1024::Parameters}::decapsulate]:
    Source: 'rust/protocol/src/kem/kyber1024.rs', lines 42:4-54:5 -/
axiom
  kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate
  :
  kem.KeyMaterial kem.Secret → Slice Std.U8 → Result (core.result.Result
    (Slice Std.U8) kem.DecapsulateError)

/-- [libsignal_protocol::kem::{impl libsignal_protocol::kem::KeyKind for libsignal_protocol::kem::Public}::key_length]:
    Source: 'rust/protocol/src/kem.rs', lines 261:4-263:5
    Visibility: public -/
axiom kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length
  : kem.KeyType → Result Std.Usize

/-- [libsignal_protocol::kem::{impl libsignal_protocol::kem::KeyKind for libsignal_protocol::kem::Secret}::key_length]:
    Source: 'rust/protocol/src/kem.rs', lines 269:4-271:5
    Visibility: public -/
axiom kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length
  : kem.KeyType → Result Std.Usize

/-- [libsignal_protocol::kem::{libsignal_protocol::kem::KeyPair}::generate]:
    Source: 'rust/protocol/src/kem.rs', lines 470:4-482:5
    Visibility: public -/
axiom kem.KeyPair.generate
  {R : Type} (rand_1rngRngInst : rand_1.rng.Rng R) (rand_core_1CryptoRngInst :
  rand_core_1.CryptoRng R) :
  kem.KeyType → R → Result (kem.KeyPair × R)

/-- [libsignal_protocol::pqxdh::{libsignal_protocol::pqxdh::HandshakeKeys}::derive]:
    Source: 'rust/protocol/src/pqxdh.rs', lines 73:4-78:5 -/
axiom pqxdh.HandshakeKeys.derive : Slice Std.U8 → Result pqxdh.HandshakeKeys

/-- [libsignal_protocol::pqxdh::{libsignal_protocol::pqxdh::HandshakeKeys}::derive_with_label]:
    Source: 'rust/protocol/src/pqxdh.rs', lines 80:4-90:5 -/
axiom pqxdh.HandshakeKeys.derive_with_label
  : Slice Std.U8 → Slice Std.U8 → Result pqxdh.HandshakeKeys

/-- [libsignal_protocol::pqxdh::{libsignal_protocol::pqxdh::InitiatorParameters}::their_one_time_pre_key]:
    Source: 'rust/protocol/src/pqxdh.rs', lines 171:4-173:5
    Visibility: public -/
axiom pqxdh.InitiatorParameters.impl.their_one_time_pre_key
  :
  pqxdh.InitiatorParameters → Result (Option libsignal_core.curve.PublicKey)

/-- [libsignal_protocol::pqxdh::{libsignal_protocol::pqxdh::RecipientParameters}::our_one_time_pre_key_pair]:
    Source: 'rust/protocol/src/pqxdh.rs', lines 297:4-299:5
    Visibility: public -/
axiom pqxdh.RecipientParameters.impl.our_one_time_pre_key_pair
  : pqxdh.RecipientParameters → Result (Option libsignal_core.curve.KeyPair)

/-- [libsignal_protocol::protocol::{impl core::convert::TryFrom<u8, derive_more::convert::try_from::TryFromReprError<u8>> for libsignal_protocol::protocol::CiphertextMessageType}::try_from]:
    Source: 'rust/protocol/src/protocol.rs', lines 30:44-30:64
    Visibility: public -/
axiom
  protocol.CiphertextMessageType.Insts.CoreConvertTryFromU8TryFromReprErrorU8.try_from
  :
  Std.U8 → Result (core.result.Result protocol.CiphertextMessageType
    (derive_more.convert.try_from.TryFromReprError Std.U8))

/-- [libsignal_protocol::protocol::log_invalid_local_addresses]:
    Source: 'rust/protocol/src/protocol.rs', lines 62:0-71:1 -/
-- Logging has no effect on protocol state or results.
def protocol.log_invalid_local_addresses
  (_sender_address _recipient_address : libsignal_core.address.ProtocolAddress) :
  Result Unit :=
  ok ()

/-- [libsignal_protocol::protocol::log_address_mismatch]:
    Source: 'rust/protocol/src/protocol.rs', lines 73:0-79:1 -/
-- Logging has no effect on protocol state or results.
def protocol.log_address_mismatch
  (_sender_address _recipient_address : libsignal_core.address.ProtocolAddress) :
  Result Unit :=
  ok ()

/-- [libsignal_protocol::protocol::{impl core::convert::TryFrom<&'_0 [u8], libsignal_protocol::error::SignalProtocolError> for libsignal_protocol::protocol::SignalMessage}::try_from]:
    Source: 'rust/protocol/src/protocol.rs', lines 272:4-315:5
    Visibility: public -/
axiom
  protocol.SignalMessage.Insts.CoreConvertTryFromShared0SliceU8SignalProtocolError.try_from
  :
  Slice Std.U8 → Result (core.result.Result protocol.SignalMessage
    error.SignalProtocolError)

/-- [libsignal_protocol::protocol::{libsignal_protocol::protocol::PreKeySignalMessage}::kyber_ciphertext]:
    Source: 'rust/protocol/src/protocol.rs', lines 415:4-417:5
    Visibility: public -/
axiom protocol.PreKeySignalMessage.kyber_ciphertext
  : protocol.PreKeySignalMessage → Result (Option (Slice Std.U8))

/-- [libsignal_protocol::protocol::{impl core::convert::TryFrom<&'_0 [u8], libsignal_protocol::error::SignalProtocolError> for libsignal_protocol::protocol::PreKeySignalMessage}::try_from]:
    Source: 'rust/protocol/src/protocol.rs', lines 449:4-516:5
    Visibility: public -/
axiom
  protocol.PreKeySignalMessage.Insts.CoreConvertTryFromShared0SliceU8SignalProtocolError.try_from
  :
  Slice Std.U8 → Result (core.result.Result protocol.PreKeySignalMessage
    error.SignalProtocolError)

/-- [libsignal_protocol::protocol::{libsignal_protocol::protocol::SenderKeyMessage}::verify_signature]:
    Source: 'rust/protocol/src/protocol.rs', lines 565:4-573:5
    Visibility: public -/
axiom protocol.SenderKeyMessage.verify_signature
  :
  protocol.SenderKeyMessage → libsignal_core.curve.PublicKey → Result
    (core.result.Result Bool error.SignalProtocolError)

/-- [libsignal_protocol::protocol::{impl core::convert::TryFrom<&'_0 [u8], libsignal_protocol::error::SignalProtocolError> for libsignal_protocol::protocol::SenderKeyMessage}::try_from]:
    Source: 'rust/protocol/src/protocol.rs', lines 615:4-657:5
    Visibility: public -/
axiom
  protocol.SenderKeyMessage.Insts.CoreConvertTryFromShared0SliceU8SignalProtocolError.try_from
  :
  Slice Std.U8 → Result (core.result.Result protocol.SenderKeyMessage
    error.SignalProtocolError)

/-- [libsignal_protocol::protocol::{impl core::convert::TryFrom<&'_0 [u8], libsignal_protocol::error::SignalProtocolError> for libsignal_protocol::protocol::SenderKeyDistributionMessage}::try_from]:
    Source: 'rust/protocol/src/protocol.rs', lines 749:4-803:5
    Visibility: public -/
axiom
  protocol.SenderKeyDistributionMessage.Insts.CoreConvertTryFromShared0SliceU8SignalProtocolError.try_from
  :
  Slice Std.U8 → Result (core.result.Result
    protocol.SenderKeyDistributionMessage error.SignalProtocolError)

/-- [libsignal_protocol::protocol::{impl core::convert::From<libsignal_protocol::protocol::DecryptionErrorMessage> for libsignal_protocol::protocol::PlaintextContent}::from]:
    Source: 'rust/protocol/src/protocol.rs', lines 836:4-849:5
    Visibility: public -/
axiom
  protocol.PlaintextContent.Insts.CoreConvertFromDecryptionErrorMessage.from
  : protocol.DecryptionErrorMessage → Result protocol.PlaintextContent

/-- [libsignal_protocol::protocol::{impl core::convert::TryFrom<&'_0 [u8], libsignal_protocol::error::SignalProtocolError> for libsignal_protocol::protocol::PlaintextContent}::try_from]:
    Source: 'rust/protocol/src/protocol.rs', lines 855:4-867:5
    Visibility: public -/
axiom
  protocol.PlaintextContent.Insts.CoreConvertTryFromShared0SliceU8SignalProtocolError.try_from
  :
  Slice Std.U8 → Result (core.result.Result protocol.PlaintextContent
    error.SignalProtocolError)

/-- [libsignal_protocol::protocol::{impl core::convert::TryFrom<&'_0 [u8], libsignal_protocol::error::SignalProtocolError> for libsignal_protocol::protocol::DecryptionErrorMessage}::try_from]:
    Source: 'rust/protocol/src/protocol.rs', lines 941:4-959:5
    Visibility: public -/
axiom
  protocol.DecryptionErrorMessage.Insts.CoreConvertTryFromShared0SliceU8SignalProtocolError.try_from
  :
  Slice Std.U8 → Result (core.result.Result protocol.DecryptionErrorMessage
    error.SignalProtocolError)

/-- [libsignal_protocol::protocol::extract_decryption_error_message_from_serialized_content]:
    Source: 'rust/protocol/src/protocol.rs', lines 963:0-980:1
    Visibility: public -/
axiom protocol.extract_decryption_error_message_from_serialized_content
  :
  Slice Std.U8 → Result (core.result.Result protocol.DecryptionErrorMessage
    error.SignalProtocolError)

/-- [libsignal_protocol::ratchet::keys::{libsignal_protocol::ratchet::keys::MessageKeys}::derive_keys]:
    Source: 'rust/protocol/src/ratchet/keys.rs', lines 100:4-122:5 -/
axiom ratchet.keys.MessageKeys.derive_keys
  :
  Slice Std.U8 → Option (Slice Std.U8) → Std.U32 → Result
    ratchet.keys.MessageKeys

/-- [libsignal_protocol::ratchet::keys::{libsignal_protocol::ratchet::keys::MessageKeyGenerator}::from_pb]:
    Source: 'rust/protocol/src/ratchet/keys.rs', lines 63:4-88:5 -/
axiom ratchet.keys.MessageKeyGenerator.from_pb
  :
  proto.storage.session_structure.chain.MessageKey → Result
    (core.result.Result ratchet.keys.MessageKeyGenerator Str)

/-- [libsignal_protocol::double_ratchet::skipped_key_from_pb]:
    Source: 'rust/protocol/src/double_ratchet.rs', lines 97:0-103:1 -/
-- Transcribes `MessageKeyGenerator::from_pb(key_pb).map(Some)
-- .map_err(InvalidSessionError)`; `InvalidSessionError` translates to `Str`.
noncomputable def double_ratchet.skipped_key_from_pb
  (key_pb : proto.storage.session_structure.chain.MessageKey) :
  Result (core.result.Result (Option ratchet.keys.MessageKeyGenerator)
    state.session.InvalidSessionError) := do
  let r ← ratchet.keys.MessageKeyGenerator.from_pb key_pb
  ok (match r with
    | .Ok key => .Ok (some key)
    | .Err message => .Err message)

/-- [libsignal_protocol::ratchet::keys::{libsignal_protocol::ratchet::keys::ChainKey}::calculate_base_material]:
    Source: 'rust/protocol/src/ratchet/keys.rs', lines 183:4-186:5 -/
axiom ratchet.keys.ChainKey.calculate_base_material
  :
  ratchet.keys.ChainKey → Array Std.U8 1#usize → Result (Array Std.U8
    32#usize)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::add_receiver_chain]:
    Source: 'rust/protocol/src/state/session.rs', lines 370:4-394:5 -/
axiom state.session.SessionState.add_receiver_chain
  :
  state.session.SessionState → libsignal_core.curve.PublicKey →
    ratchet.keys.ChainKey → Result state.session.SessionState

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::new]:
    Source: 'rust/protocol/src/state/session.rs', lines 174:4-199:5 -/
axiom state.session.SessionState.new
  :
  Std.U8 → identity_key.IdentityKey → identity_key.IdentityKey →
    ratchet.keys.RootKey → libsignal_core.curve.PublicKey → alloc.vec.Vec
    Std.U8 → Result state.session.SessionState

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::new]:
    Source: 'rust/protocol/src/state/session.rs', lines 746:4-751:5 -/
axiom state.session.SessionRecord.new
  : state.session.SessionState → Result state.session.SessionRecord

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderMessageKey}::new]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 34:4-45:5 -/
axiom sender_keys.SenderMessageKey.new
  : Std.U32 → alloc.vec.Vec Std.U8 → Result sender_keys.SenderMessageKey

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderChainKey}::new]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 85:4-90:5 -/
axiom sender_keys.SenderChainKey.new
  : Std.U32 → alloc.vec.Vec Std.U8 → Result sender_keys.SenderChainKey

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderChainKey}::next]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 100:4-112:5 -/
axiom sender_keys.SenderChainKey.next
  :
  sender_keys.SenderChainKey → Result (core.result.Result
    sender_keys.SenderChainKey error.SignalProtocolError)

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderKeyState}::new]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 137:4-164:5 -/
axiom sender_keys.SenderKeyState.new
  :
  Std.U8 → Std.U32 → Std.U32 → Slice Std.U8 →
    libsignal_core.curve.PublicKey → Option libsignal_core.curve.PrivateKey
    → Result sender_keys.SenderKeyState

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderKeyState}::signing_key_public]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 193:4-200:5 -/
axiom sender_keys.SenderKeyState.signing_key_public
  :
  sender_keys.SenderKeyState → Result (core.result.Result
    libsignal_core.curve.PublicKey sender_keys.InvalidSessionError)

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderKeyState}::signing_key_private]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 202:4-209:5 -/
axiom sender_keys.SenderKeyState.signing_key_private
  :
  sender_keys.SenderKeyState → Result (core.result.Result
    libsignal_core.curve.PrivateKey sender_keys.InvalidSessionError)

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderKeyRecord}::sender_key_state]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 262:4-267:5 -/
axiom sender_keys.SenderKeyRecord.sender_key_state
  :
  sender_keys.SenderKeyRecord → Result (core.result.Result
    sender_keys.SenderKeyState sender_keys.InvalidSessionError)

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderKeyRecord}::sender_key_state_mut]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 269:4-276:5 -/
axiom sender_keys.SenderKeyRecord.sender_key_state_mut
  :
  sender_keys.SenderKeyRecord → Result ((core.result.Result
    sender_keys.SenderKeyState sender_keys.InvalidSessionError) ×
    (core.result.Result sender_keys.SenderKeyState
    sender_keys.InvalidSessionError → sender_keys.SenderKeyRecord))

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderKeyRecord}::add_sender_key_state]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 294:4-328:5 -/
axiom sender_keys.SenderKeyRecord.add_sender_key_state
  :
  sender_keys.SenderKeyRecord → Std.U8 → Std.U32 → Std.U32 → Slice
    Std.U8 → libsignal_core.curve.PublicKey → Option
    libsignal_core.curve.PrivateKey → Result sender_keys.SenderKeyRecord

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderKeyRecord}::remove_state]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 333:4-339:5 -/
axiom sender_keys.SenderKeyRecord.remove_state
  :
  sender_keys.SenderKeyRecord → Std.U32 → libsignal_core.curve.PublicKey
    → Result ((Option sender_keys.SenderKeyState) ×
    sender_keys.SenderKeyRecord)

/-- [libsignal_protocol::sender_keys::{libsignal_protocol::sender_keys::SenderKeyRecord}::remove_states_with_chain_id]:
    Source: 'rust/protocol/src/sender_keys.rs', lines 344:4-348:5 -/
axiom sender_keys.SenderKeyRecord.remove_states_with_chain_id
  :
  sender_keys.SenderKeyRecord → Std.U32 → Result (Std.Usize ×
    sender_keys.SenderKeyRecord)

/-- [libsignal_protocol::session_management::try_decrypt_from_record]:
    Source: 'rust/protocol/src/session_management.rs', lines 379:0-567:1 -/
axiom session_management.try_decrypt_from_record
  {R : Type} (rand_1rngRngInst : rand_1.rng.Rng R) (rand_core_1CryptoRngInst :
  rand_core_1.CryptoRng R) :
  state.session.SessionRecord → libsignal_core.address.ProtocolAddress →
    libsignal_core.address.ProtocolAddress → protocol.SignalMessage →
    protocol.CiphertextMessageType → R → Result ((core.result.Result
    (alloc.vec.Vec Std.U8) error.SignalProtocolError) ×
    state.session.SessionRecord × R)

/-- [libsignal_protocol::session_management::try_decrypt_with_state]:
    Source: 'rust/protocol/src/session_management.rs', lines 577:0-617:1 -/
axiom session_management.try_decrypt_with_state
  {R : Type} (rand_1rngRngInst : rand_1.rng.Rng R) (rand_core_1CryptoRngInst :
  rand_core_1.CryptoRng R) :
  state.session.SessionState → libsignal_core.address.ProtocolAddress →
    libsignal_core.address.ProtocolAddress → protocol.SignalMessage →
    protocol.CiphertextMessageType → session_management.CurrentOrPrevious →
    R → Result ((core.result.Result (alloc.vec.Vec Std.U8)
    error.SignalProtocolError) × state.session.SessionState × R)

/-- [libsignal_protocol::session_management::format_decryption_failure_log]:
    Source: 'rust/protocol/src/session_management.rs', lines 621:0-709:1 -/
axiom session_management.format_decryption_failure_log
  :
  libsignal_core.address.ProtocolAddress → Slice error.SignalProtocolError
    → state.session.SessionRecord → protocol.SignalMessage → Result
    (core.result.Result String error.SignalProtocolError)

/-- [libsignal_protocol::state::bundle::{libsignal_protocol::state::bundle::PreKeyBundle}::modify]:
    Source: 'rust/protocol/src/state/bundle.rs', lines 221:4-228:5
    Visibility: public -/
axiom state.bundle.PreKeyBundle.modify
  {F : Type} (coreopsfunctionFnOnceFTupleMutPreKeyBundleContentTupleInst :
  core.ops.function.FnOnce F state.bundle.PreKeyBundleContent Unit) :
  state.bundle.PreKeyBundle → F → Result (core.result.Result
    state.bundle.PreKeyBundle error.SignalProtocolError)

/-- [libsignal_protocol::state::signed_prekey::GenericSignedPreKey::deserialize]:
    Source: 'rust/protocol/src/state/signed_prekey.rs', lines 80:4-88:5
    Visibility: public -/
-- Opaque default indexed by the types instead of the instance. Rust coherence
-- allows at most one impl of a trait per type, so this is as general as one
-- external per impl, and `impl_def` can close the instance.
axiom state.signed_prekey.GenericSignedPreKey.deserialize.external
  {Self : Type} {Clause0_KeyPair : Type} {Clause0_Id : Type}
  {Clause0_Clause0_PublicKey : Type} {Clause0_Clause0_PrivateKey : Type} :
  Slice Std.U8 → Result (core.result.Result Self error.SignalProtocolError)

@[trait_default]
noncomputable def state.signed_prekey.GenericSignedPreKey.deserialize.default
  {Self : Type} {Clause0_KeyPair : Type} {Clause0_Id : Type}
  {Clause0_Clause0_PublicKey : Type} {Clause0_Clause0_PrivateKey : Type}
  (GenericSignedPreKeyInst : state.signed_prekey.GenericSignedPreKey Self
  Clause0_KeyPair Clause0_Id Clause0_Clause0_PublicKey
  Clause0_Clause0_PrivateKey) :
  Slice Std.U8 → Result (core.result.Result Self error.SignalProtocolError) :=
  state.signed_prekey.GenericSignedPreKey.deserialize.external
    (Clause0_KeyPair := Clause0_KeyPair) (Clause0_Id := Clause0_Id)
    (Clause0_Clause0_PublicKey := Clause0_Clause0_PublicKey)
    (Clause0_Clause0_PrivateKey := Clause0_Clause0_PrivateKey)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::UnacknowledgedPreKeyMessageItems<'a>}::new]:
    Source: 'rust/protocol/src/state/session.rs', lines 55:4-73:5 -/
axiom state.session.UnacknowledgedPreKeyMessageItems.new
  :
  Option state.prekey.PreKeyId → state.signed_prekey.SignedPreKeyId →
    libsignal_core.curve.PublicKey → Option
    proto.storage.session_structure.PendingKyberPreKey → std.time.SystemTime
    → Result state.session.UnacknowledgedPreKeyMessageItems

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::alice_base_key]:
    Source: 'rust/protocol/src/state/session.rs', lines 201:4-204:5 -/
axiom state.session.SessionState.alice_base_key
  : state.session.SessionState → Result (Slice Std.U8)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::session_version]:
    Source: 'rust/protocol/src/state/session.rs', lines 206:4-211:5 -/
axiom state.session.SessionState.session_version
  :
  state.session.SessionState → Result (core.result.Result Std.U32
    state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::remote_identity_key]:
    Source: 'rust/protocol/src/state/session.rs', lines 213:4-221:5 -/
axiom state.session.SessionState.remote_identity_key
  :
  state.session.SessionState → Result (core.result.Result (Option
    identity_key.IdentityKey) state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::remote_identity_key_bytes]:
    Source: 'rust/protocol/src/state/session.rs', lines 223:4-225:5 -/
axiom state.session.SessionState.remote_identity_key_bytes
  :
  state.session.SessionState → Result (core.result.Result (Option
    (alloc.vec.Vec Std.U8)) state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::local_identity_key]:
    Source: 'rust/protocol/src/state/session.rs', lines 227:4-230:5 -/
axiom state.session.SessionState.local_identity_key
  :
  state.session.SessionState → Result (core.result.Result
    identity_key.IdentityKey state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::local_identity_key_bytes]:
    Source: 'rust/protocol/src/state/session.rs', lines 232:4-234:5 -/
axiom state.session.SessionState.local_identity_key_bytes
  :
  state.session.SessionState → Result (core.result.Result (alloc.vec.Vec
    Std.U8) state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::sender_ratchet_key]:
    Source: 'rust/protocol/src/state/session.rs', lines 270:4-276:5 -/
axiom state.session.SessionState.sender_ratchet_key
  :
  state.session.SessionState → Result (core.result.Result
    libsignal_core.curve.PublicKey state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::sender_ratchet_private_key]:
    Source: 'rust/protocol/src/state/session.rs', lines 282:4-288:5 -/
axiom state.session.SessionState.sender_ratchet_private_key
  :
  state.session.SessionState → Result (core.result.Result
    libsignal_core.curve.PrivateKey state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::has_usable_sender_chain]:
    Source: 'rust/protocol/src/state/session.rs', lines 290:4-320:5
    Visibility: public -/
axiom state.session.SessionState.has_usable_sender_chain
  :
  state.session.SessionState → std.time.SystemTime →
    state.session.SessionUsabilityRequirements → Result (core.result.Result
    Bool state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::get_receiver_chain]:
    Source: 'rust/protocol/src/state/session.rs', lines 334:4-350:5 -/
axiom state.session.SessionState.get_receiver_chain
  :
  state.session.SessionState → libsignal_core.curve.PublicKey → Result
    (core.result.Result (Option (proto.storage.session_structure.Chain ×
    Std.Usize)) state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::get_receiver_chain_key]:
    Source: 'rust/protocol/src/state/session.rs', lines 352:4-368:5 -/
axiom state.session.SessionState.get_receiver_chain_key
  :
  state.session.SessionState → libsignal_core.curve.PublicKey → Result
    (core.result.Result (Option ratchet.keys.ChainKey)
    state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::get_sender_chain_key]:
    Source: 'rust/protocol/src/state/session.rs', lines 422:4-439:5 -/
axiom state.session.SessionState.get_sender_chain_key
  :
  state.session.SessionState → Result (core.result.Result
    ratchet.keys.ChainKey state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::get_sender_chain_key_bytes]:
    Source: 'rust/protocol/src/state/session.rs', lines 441:4-443:5 -/
axiom state.session.SessionState.get_sender_chain_key_bytes
  :
  state.session.SessionState → Result (core.result.Result (alloc.vec.Vec
    Std.U8) state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::unacknowledged_pre_key_message_items]:
    Source: 'rust/protocol/src/state/session.rs', lines 577:4-592:5 -/
axiom state.session.SessionState.unacknowledged_pre_key_message_items
  :
  state.session.SessionState → Result (core.result.Result (Option
    state.session.UnacknowledgedPreKeyMessageItems)
    state.session.InvalidSessionError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::remote_registration_id]:
    Source: 'rust/protocol/src/state/session.rs', lines 623:4-625:5 -/
axiom state.session.SessionState.remote_registration_id
  : state.session.SessionState → Result Std.U32

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::local_registration_id]:
    Source: 'rust/protocol/src/state/session.rs', lines 631:4-633:5 -/
axiom state.session.SessionState.local_registration_id
  : state.session.SessionState → Result Std.U32

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionState}::get_kyber_ciphertext]:
    Source: 'rust/protocol/src/state/session.rs', lines 635:4-640:5 -/
axiom state.session.SessionState.get_kyber_ciphertext
  : state.session.SessionState → Result (Option (alloc.vec.Vec Std.U8))

/-- [libsignal_protocol::state::session::{impl core::convert::From<libsignal_protocol::proto::storage::SessionStructure> for libsignal_protocol::state::session::SessionState}::from]:
    Source: 'rust/protocol/src/state/session.rs', lines 715:4-717:5
    Visibility: public -/
axiom state.session.SessionState.Insts.CoreConvertFromSessionStructure.from
  : proto.storage.SessionStructure → Result state.session.SessionState

/-- [libsignal_protocol::state::session::{impl core::convert::From<libsignal_protocol::state::session::SessionState> for libsignal_protocol::proto::storage::SessionStructure}::from]:
    Source: 'rust/protocol/src/state/session.rs', lines 721:4-723:5
    Visibility: public -/
axiom proto.storage.SessionStructure.Insts.CoreConvertFromSessionState.from
  : state.session.SessionState → Result proto.storage.SessionStructure

/-- [libsignal_protocol::state::session::{impl core::convert::From<&'_0 libsignal_protocol::state::session::SessionState> for libsignal_protocol::proto::storage::SessionStructure}::from]:
    Source: 'rust/protocol/src/state/session.rs', lines 727:4-729:5
    Visibility: public -/
axiom
  proto.storage.SessionStructure.Insts.CoreConvertFromShared0SessionState.from
  : state.session.SessionState → Result proto.storage.SessionStructure

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::deserialize]:
    Source: 'rust/protocol/src/state/session.rs', lines 753:4-761:5
    Visibility: public -/
axiom state.session.SessionRecord.deserialize
  :
  Slice Std.U8 → Result (core.result.Result state.session.SessionRecord
    error.SignalProtocolError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::previous_session_states]:
    Source: 'rust/protocol/src/state/session.rs', lines 815:4-823:5 -/
axiom state.session.SessionRecord.previous_session_states
  :
  state.session.SessionRecord → Result (core.iter.adapters.map.Map
    (core.slice.iter.Iter (alloc.vec.Vec Std.U8))
    state.session.SessionRecord.previous_session_states.closure)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::archive_current_state]:
    Source: 'rust/protocol/src/state/session.rs', lines 856:4-861:5
    Visibility: public -/
axiom state.session.SessionRecord.archive_current_state
  :
  state.session.SessionRecord → Result ((core.result.Result Unit
    error.SignalProtocolError) × state.session.SessionRecord)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::current_pq_state]:
    Source: 'rust/protocol/src/state/session.rs', lines 871:4-873:5
    Visibility: public -/
axiom state.session.SessionRecord.current_pq_state
  : state.session.SessionRecord → Result (Option (alloc.vec.Vec Std.U8))

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::remote_registration_id]:
    Source: 'rust/protocol/src/state/session.rs', lines 875:4-884:5
    Visibility: public -/
axiom state.session.SessionRecord.remote_registration_id
  :
  state.session.SessionRecord → Result (core.result.Result Std.U32
    error.SignalProtocolError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::local_registration_id]:
    Source: 'rust/protocol/src/state/session.rs', lines 886:4-895:5
    Visibility: public -/
axiom state.session.SessionRecord.local_registration_id
  :
  state.session.SessionRecord → Result (core.result.Result Std.U32
    error.SignalProtocolError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::session_version]:
    Source: 'rust/protocol/src/state/session.rs', lines 897:4-906:5
    Visibility: public -/
axiom state.session.SessionRecord.session_version
  :
  state.session.SessionRecord → Result (core.result.Result Std.U32
    error.SignalProtocolError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::local_identity_key_bytes]:
    Source: 'rust/protocol/src/state/session.rs', lines 908:4-917:5
    Visibility: public -/
axiom state.session.SessionRecord.local_identity_key_bytes
  :
  state.session.SessionRecord → Result (core.result.Result (alloc.vec.Vec
    Std.U8) error.SignalProtocolError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::remote_identity_key_bytes]:
    Source: 'rust/protocol/src/state/session.rs', lines 919:4-928:5
    Visibility: public -/
axiom state.session.SessionRecord.remote_identity_key_bytes
  :
  state.session.SessionRecord → Result (core.result.Result (Option
    (alloc.vec.Vec Std.U8)) error.SignalProtocolError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::has_usable_sender_chain]:
    Source: 'rust/protocol/src/state/session.rs', lines 930:4-939:5
    Visibility: public -/
axiom state.session.SessionRecord.has_usable_sender_chain
  :
  state.session.SessionRecord → std.time.SystemTime →
    state.session.SessionUsabilityRequirements → Result (core.result.Result
    Bool error.SignalProtocolError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::alice_base_key]:
    Source: 'rust/protocol/src/state/session.rs', lines 941:4-950:5
    Visibility: public -/
axiom state.session.SessionRecord.alice_base_key
  :
  state.session.SessionRecord → Result (core.result.Result (Slice Std.U8)
    error.SignalProtocolError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::get_receiver_chain_key_bytes]:
    Source: 'rust/protocol/src/state/session.rs', lines 952:4-965:5
    Visibility: public -/
axiom state.session.SessionRecord.get_receiver_chain_key_bytes
  :
  state.session.SessionRecord → libsignal_core.curve.PublicKey → Result
    (core.result.Result (Option (Slice Std.U8)) error.SignalProtocolError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::get_sender_chain_key_bytes]:
    Source: 'rust/protocol/src/state/session.rs', lines 967:4-976:5
    Visibility: public -/
axiom state.session.SessionRecord.get_sender_chain_key_bytes
  :
  state.session.SessionRecord → Result (core.result.Result (alloc.vec.Vec
    Std.U8) error.SignalProtocolError)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::get_kyber_ciphertext]:
    Source: 'rust/protocol/src/state/session.rs', lines 988:4-997:5
    Visibility: public -/
axiom state.session.SessionRecord.get_kyber_ciphertext
  :
  state.session.SessionRecord → Result (core.result.Result (Option
    (alloc.vec.Vec Std.U8)) error.SignalProtocolError)



/-- [libsignal_protocol::triple_ratchet::log_sender_chain_corrupt]:
    Source: 'rust/protocol/src/triple_ratchet.rs', lines 37:0-39:1 -/
-- Logging has no effect on protocol state or results.
def triple_ratchet.log_sender_chain_corrupt
  (_remote_address : libsignal_core.address.ProtocolAddress) : Result Unit :=
  ok ()

/-- [libsignal_protocol::triple_ratchet::is_bad_key_or_iv]:
    Source: 'rust/protocol/src/triple_ratchet.rs', lines 63:0-65:1 -/
-- Transcribes `matches!(error, DecryptionError::BadKeyOrIv)`.
def triple_ratchet.is_bad_key_or_iv
  (error : signal_crypto.aes_cbc.DecryptionError) : Result Bool :=
  ok (match error with
    | .BadKeyOrIv => true
    | _ => false)

/-- [libsignal_protocol::triple_ratchet::decrypt_failure_message]:
    Source: 'rust/protocol/src/triple_ratchet.rs', lines 68:0-75:1 -/
axiom triple_ratchet.decrypt_failure_message
  : signal_crypto.aes_cbc.DecryptionError → Result String

/-- [libsignal_protocol::triple_ratchet::is_state_decode]:
    Source: 'rust/protocol/src/triple_ratchet.rs', lines 79:0-81:1 -/
-- Transcribes `matches!(error, spqr::Error::StateDecode)`.
def triple_ratchet.is_state_decode (error : spqr.Error) : Result Bool :=
  ok (match error with
    | .StateDecode => true
    | _ => false)

/-- [libsignal_protocol::triple_ratchet::log_receiver_chain_corrupt]:
    Source: 'rust/protocol/src/triple_ratchet.rs', lines 41:0-46:1 -/
-- Logging has no effect on protocol state or results.
def triple_ratchet.log_receiver_chain_corrupt
  (_current_or_previous : session_management.CurrentOrPrevious)
  (_sender_address : libsignal_core.address.ProtocolAddress) : Result Unit :=
  ok ()
