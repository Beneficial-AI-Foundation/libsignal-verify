-- [libsignal_core]: external functions.
import Aeneas
import Translation.Core.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
set_option linter.style.whitespace false
open libsignal_core

/-- [core::array::equality::{impl core::cmp::PartialEq<[U; N]> for [T]}::eq]:
    Source: '/rustc/library/core/src/array/equality.rs', lines 48:4-48:40
    Name pattern: [core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq]
    Visibility: public -/
@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq"]
axiom Slice.Insts.CoreCmpPartialEqArray.eq
  {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U) :
  Slice T → Array U N → Result Bool

/-- [core::num::niche_types::{impl core::clone::Clone for core::num::niche_types::NonZeroU64Inner}::clone]:
    Source: '/rustc/library/core/src/num/niche_types.rs', lines 17:17-17:22
    Name pattern: [core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU64Inner>}::clone]
    Visibility: public -/
@[rust_fun
  "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU64Inner>}::clone"]
axiom core.num.niche_types.NonZeroU64Inner.Insts.CoreCloneClone.clone
  :
  core.num.niche_types.NonZeroU64Inner → Result
    core.num.niche_types.NonZeroU64Inner

/-- [core::num::niche_types::{impl core::clone::Clone for core::num::niche_types::NonZeroU8Inner}::clone]:
    Source: '/rustc/library/core/src/num/niche_types.rs', lines 17:17-17:22
    Name pattern: [core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU8Inner>}::clone]
    Visibility: public -/
@[rust_fun
  "core::num::niche_types::{core::clone::Clone<core::num::niche_types::NonZeroU8Inner>}::clone"]
axiom core.num.niche_types.NonZeroU8Inner.Insts.CoreCloneClone.clone
  :
  core.num.niche_types.NonZeroU8Inner → Result
    core.num.niche_types.NonZeroU8Inner

/-- [core::num::nonzero::{core::num::nonzero::NonZero<T, Clause0_NonZeroInner>}::new]:
    Source: '/rustc/library/core/src/num/nonzero.rs', lines 404:4-404:42
    Name pattern: [core::num::nonzero::{core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>}::new]
    Visibility: public -/
@[rust_fun
  "core::num::nonzero::{core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>}::new"]
axiom core.num.nonzero.NonZero.new
  {T : Type} {Clause0_NonZeroInner : Type} (ZeroablePrimitiveInst :
  core.num.nonzero.ZeroablePrimitive T Clause0_NonZeroInner) :
  T → Result (Option (core.num.nonzero.NonZero T Clause0_NonZeroInner))

/-- [core::num::nonzero::{core::num::nonzero::NonZero<T, Clause0_NonZeroInner>}::get]:
    Source: '/rustc/library/core/src/num/nonzero.rs', lines 483:4-483:31
    Name pattern: [core::num::nonzero::{core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>}::get]
    Visibility: public -/
@[rust_fun
  "core::num::nonzero::{core::num::nonzero::NonZero<@T, @Clause0_NonZeroInner>}::get"]
axiom core.num.nonzero.NonZero.get
  {T : Type} {Clause0_NonZeroInner : Type} (ZeroablePrimitiveInst :
  core.num.nonzero.ZeroablePrimitive T Clause0_NonZeroInner) :
  core.num.nonzero.NonZero T Clause0_NonZeroInner → Result T

-- core::option::Option::map is shared; imported from Translation.Shared.Core.Externals.

-- core::option Try::branch + FromResidual::from_residual are shared (Translation.Shared.Core).

/-- [core::result::{core::result::Result<T, E>}::ok]:
    Source: '/rustc/library/core/src/result.rs', lines 708:4-711:28
    Name pattern: [core::result::{core::result::Result<@T, @E>}::ok]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
axiom core.result.Result.ok
  {T : Type} {E : Type} : core.result.Result T E → Result (Option T)

-- core::result Try::branch + FromResidual::from_residual are shared (Translation.Shared.Core).

/-- [alloc::string::{impl core::ops::deref::Deref<str> for alloc::string::String}::deref]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2835:4-2835:27
    Name pattern: [alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref]
    Visibility: public -/
@[rust_fun
  "alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref"]
axiom alloc.string.String.Insts.CoreOpsDerefDerefStr.deref
  : String → Result Str

-- alloc::vec::Vec::into_boxed_slice is shared; imported from Translation.Shared.Alloc.Externals.

/-- [derive_more::convert::try_from::{derive_more::convert::try_from::TryFromReprError<T>}::new]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/derive_more-2.1.1/src/convert.rs', lines 29:8-29:42
    Name pattern: [derive_more::convert::try_from::{derive_more::convert::try_from::TryFromReprError<@T>}::new]
    Visibility: public -/
@[rust_fun
  "derive_more::convert::try_from::{derive_more::convert::try_from::TryFromReprError<@T>}::new"]
axiom derive_more.convert.try_from.TryFromReprError.new
  {T : Type} : T → Result (derive_more.convert.try_from.TryFromReprError T)

/-- [uuid::builder::{uuid::Uuid}::from_slice]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/uuid-1.19.0/src/builder.rs', lines 287:4-287:54
    Name pattern: [uuid::builder::{uuid::Uuid}::from_slice]
    Visibility: public -/
@[rust_fun "uuid::builder::{uuid::Uuid}::from_slice"]
axiom uuid.builder.Uuid.from_slice
  : Slice Std.U8 → Result (core.result.Result uuid.Uuid uuid.error.Error)

/-- [uuid::builder::{uuid::Uuid}::from_bytes]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/uuid-1.19.0/src/builder.rs', lines 364:4-364:49
    Name pattern: [uuid::builder::{uuid::Uuid}::from_bytes]
    Visibility: public -/
@[rust_fun "uuid::builder::{uuid::Uuid}::from_bytes"]
axiom uuid.builder.Uuid.from_bytes : Array Std.U8 16#usize → Result uuid.Uuid

/-- [libsignal_core::curve::{libsignal_core::curve::PublicKey}::deserialize]:
    Source: 'rust/core/src/curve.rs', lines 84:4-105:5
    Visibility: public -/
axiom curve.PublicKey.deserialize
  :
  Slice Std.U8 → Result (core.result.Result curve.PublicKey curve.CurveError)

/-- [libsignal_core::curve::{libsignal_core::curve::PublicKey}::verify_signature_for_multipart_message]:
    Source: 'rust/core/src/curve.rs', lines 138:4-151:5
    Visibility: public -/
axiom curve.PublicKey.verify_signature_for_multipart_message
  : curve.PublicKey → Slice (Slice Std.U8) → Slice Std.U8 → Result Bool

/-- [libsignal_core::curve::{libsignal_core::curve::PublicKey}::is_torsion_free]:
    Source: 'rust/core/src/curve.rs', lines 165:4-174:5 -/
axiom curve.PublicKey.is_torsion_free : curve.PublicKey → Result Bool

/-- [libsignal_core::curve::{impl core::convert::TryFrom<&'_0 [u8], libsignal_core::curve::CurveError> for libsignal_core::curve::PublicKey}::try_from]:
    Source: 'rust/core/src/curve.rs', lines 196:4-198:5
    Visibility: public -/
axiom curve.PublicKey.Insts.CoreConvertTryFromShared0SliceU8CurveError.try_from
  :
  Slice Std.U8 → Result (core.result.Result curve.PublicKey curve.CurveError)

/-- [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::deserialize]:
    Source: 'rust/core/src/curve.rs', lines 242:4-251:5
    Visibility: public -/
axiom curve.PrivateKey.deserialize
  :
  Slice Std.U8 → Result (core.result.Result curve.PrivateKey
    curve.CurveError)

/-- [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::public_key]:
    Source: 'rust/core/src/curve.rs', lines 259:4-267:5
    Visibility: public -/
axiom curve.PrivateKey.public_key
  :
  curve.PrivateKey → Result (core.result.Result curve.PublicKey
    curve.CurveError)

/-- [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::calculate_signature]:
    Source: 'rust/core/src/curve.rs', lines 275:4-281:5
    Visibility: public -/
axiom curve.PrivateKey.calculate_signature
  {R : Type} (rand_core_1CryptoRngInst : rand_core_1.CryptoRng R)
  (randrngRngInst : rand.rng.Rng R) :
  curve.PrivateKey → Slice Std.U8 → R → Result ((core.result.Result
    (Slice Std.U8) curve.CurveError) × R)

/-- [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::calculate_signature_for_multipart_message]:
    Source: 'rust/core/src/curve.rs', lines 283:4-294:5
    Visibility: public -/
axiom curve.PrivateKey.calculate_signature_for_multipart_message
  {R : Type} (rand_core_1CryptoRngInst : rand_core_1.CryptoRng R)
  (randrngRngInst : rand.rng.Rng R) :
  curve.PrivateKey → Slice (Slice Std.U8) → R → Result
    ((core.result.Result (Slice Std.U8) curve.CurveError) × R)

/-- [libsignal_core::curve::{libsignal_core::curve::PrivateKey}::calculate_agreement]:
    Source: 'rust/core/src/curve.rs', lines 296:4-309:5
    Visibility: public -/
axiom curve.PrivateKey.calculate_agreement
  :
  curve.PrivateKey → curve.PublicKey → Result (core.result.Result (Slice
    Std.U8) curve.CurveError)

/-- [libsignal_core::curve::{impl core::convert::TryFrom<&'_0 [u8], libsignal_core::curve::CurveError> for libsignal_core::curve::PrivateKey}::try_from]:
    Source: 'rust/core/src/curve.rs', lines 315:4-317:5
    Visibility: public -/
axiom
  curve.PrivateKey.Insts.CoreConvertTryFromShared0SliceU8CurveError.try_from
  :
  Slice Std.U8 → Result (core.result.Result curve.PrivateKey
    curve.CurveError)

/-- [libsignal_core::curve::{libsignal_core::curve::KeyPair}::generate]:
    Source: 'rust/core/src/curve.rs', lines 327:4-341:5
    Visibility: public -/
axiom curve.KeyPair.generate
  {R : Type} (randrngRngInst : rand.rng.Rng R) (rand_core_1CryptoRngInst :
  rand_core_1.CryptoRng R) :
  R → Result (curve.KeyPair × R)

/-- [libsignal_core::curve::{libsignal_core::curve::KeyPair}::calculate_signature]:
    Source: 'rust/core/src/curve.rs', lines 362:4-368:5
    Visibility: public -/
axiom curve.KeyPair.calculate_signature
  {R : Type} (rand_core_1CryptoRngInst : rand_core_1.CryptoRng R)
  (randrngRngInst : rand.rng.Rng R) :
  curve.KeyPair → Slice Std.U8 → R → Result ((core.result.Result (Slice
    Std.U8) curve.CurveError) × R)

/-- [libsignal_core::curve::{libsignal_core::curve::KeyPair}::calculate_agreement]:
    Source: 'rust/core/src/curve.rs', lines 370:4-372:5
    Visibility: public -/
axiom curve.KeyPair.calculate_agreement
  :
  curve.KeyPair → curve.PublicKey → Result (core.result.Result (Slice
    Std.U8) curve.CurveError)
