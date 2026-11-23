-- [libsignal_core]: external functions.
import Aeneas
import Libsignal.Translated.Core.Types
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

-- core::option::Option::map is shared; imported from Libsignal.Translated.Shared.Core.

-- core::option Try::branch + FromResidual::from_residual are shared (Libsignal.Translated.Shared.Core).

/-- [core::result::{core::result::Result<T, E>}::ok]:
    Source: '/rustc/library/core/src/result.rs', lines 708:4-711:28
    Name pattern: [core::result::{core::result::Result<@T, @E>}::ok]
    Visibility: public -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
axiom core.result.Result.ok
  {T : Type} {E : Type} : core.result.Result T E → Result (Option T)

-- core::result Try::branch + FromResidual::from_residual are shared (Libsignal.Translated.Shared.Core).

/-- [core::slice::{[T]}::split_first]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 200:4-200:57
    Name pattern: [core::slice::{[@T]}::split_first]
    Visibility: public -/
@[rust_fun "core::slice::{[@T]}::split_first"]
axiom core.slice.Slice.split_first
  {T : Type _} : Slice T → Result (Option (T × (Slice T)))

/-- [core::slice::{[T]}::split_first_chunk]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 389:4-389:84
    Name pattern: [core::slice::{[@T]}::split_first_chunk]
    Visibility: public -/
@[rust_fun "core::slice::{[@T]}::split_first_chunk"]
axiom core.slice.Slice.split_first_chunk
  {T : Type _} (N : Std.Usize) :
  Slice T → Result (Option ((Array T N) × (Slice T)))

/-- [core::str::{str}::len]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 155:4-155:36
    Name pattern: [core::str::{str}::len]
    Visibility: public -/
@[rust_fun "core::str::{str}::len"]
axiom core.str.Str.len : Str → Result Std.Usize

/-- [core::str::{str}::as_bytes]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 514:4-514:41
    Name pattern: [core::str::{str}::as_bytes]
    Visibility: public -/
@[rust_fun "core::str::{str}::as_bytes"]
axiom core.str.Str.as_bytes : Str → Result (Slice Std.U8)

/-- [core::str::{str}::split_at]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 860:4-860:60
    Name pattern: [core::str::{str}::split_at]
    Visibility: public -/
@[rust_fun "core::str::{str}::split_at"]
axiom core.str.Str.split_at : Str → Std.Usize → Result (Str × Str)

/-- [alloc::string::{impl core::clone::Clone for alloc::string::String}::clone]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2425:4-2425:27
    Name pattern: [alloc::string::{core::clone::Clone<alloc::string::String>}::clone]
    Visibility: public -/
-- The clone holds the same characters as the original.
@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (s : String) : Result String :=
  ok s

/-- [alloc::string::{impl core::ops::deref::Deref<str> for alloc::string::String}::deref]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2835:4-2835:27
    Name pattern: [alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref]
    Visibility: public -/
@[rust_fun
  "alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref"]
axiom alloc.string.String.Insts.CoreOpsDerefDerefStr.deref
  : String → Result Str

-- alloc::vec::Vec::into_boxed_slice is shared; imported from Libsignal.Translated.Shared.Alloc.

/-- [curve25519_dalek::scalar::clamp_integer]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/curve25519-dalek-5.0.0/src/scalar.rs', lines 1407:0-1407:59
    Name pattern: [curve25519_dalek::scalar::clamp_integer]
    Visibility: public -/
@[rust_fun "curve25519_dalek::scalar::clamp_integer"]
axiom curve25519_dalek.scalar.clamp_integer
  : Array Std.U8 32#usize → Result (Array Std.U8 32#usize)

/-- [derive_more::convert::try_from::{derive_more::convert::try_from::TryFromReprError<T>}::new]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/derive_more-2.1.1/src/convert.rs', lines 29:8-29:42
    Name pattern: [derive_more::convert::try_from::{derive_more::convert::try_from::TryFromReprError<@T>}::new]
    Visibility: public -/
@[rust_fun
  "derive_more::convert::try_from::{derive_more::convert::try_from::TryFromReprError<@T>}::new"]
def libsignal_core.derive_more.convert.try_from.TryFromReprError.new
  {T : Type} (input : T) :
  Result (libsignal_core.derive_more.convert.try_from.TryFromReprError T) :=
  ok { input }

-- (dropped axiom Bool.Insts.CoreConvertFromChoice.from; provided by an imported sibling lib)

-- (dropped axiom Slice.Insts.SubtleConstantTimeEq.ct_eq; provided by an imported sibling lib)

-- (dropped axiom U8.Insts.SubtleConstantTimeEq.ct_eq; provided by an imported sibling lib)

/-- [subtle::{impl subtle::ConstantTimeEq for i32}::ct_eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 362:12-362:51; this code is generated from a macro invocation at: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 372:0-372:37
    Name pattern: [subtle::{subtle::ConstantTimeEq<i32>}::ct_eq]
    Visibility: public -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<i32>}::ct_eq"]
axiom I32.Insts.SubtleConstantTimeEq.ct_eq
  : Std.I32 → Std.I32 → Result subtle.Choice

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

/-- [uuid::fmt::{uuid::fmt::Hyphenated}::LENGTH]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/uuid-1.23.4/src/fmt.rs', lines 292:4-292:27
    Name pattern: [uuid::fmt::{uuid::fmt::Hyphenated}::LENGTH]
    Visibility: public -/
-- uuid 1.23.4 declares `pub const LENGTH: usize = 36;`, the length of a hyphenated UUID string.
@[rust_const "uuid::fmt::{uuid::fmt::Hyphenated}::LENGTH"]
def uuid.fmt.Hyphenated.LENGTH : Result Std.Usize :=
  ok 36#usize

/-- [uuid::{impl core::cmp::PartialEq<uuid::Uuid> for uuid::Uuid}::eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/uuid-1.23.4/src/lib.rs', lines 446:31-446:40
    Name pattern: [uuid::{core::cmp::PartialEq<uuid::Uuid, uuid::Uuid>}::eq]
    Visibility: public -/
-- `Uuid` is `struct Uuid([u8; 16])` with a derived `PartialEq`, which compares the 16 bytes.
@[rust_fun "uuid::{core::cmp::PartialEq<uuid::Uuid, uuid::Uuid>}::eq"]
def uuid.Uuid.Insts.CoreCmpPartialEqUuid.eq (self other : uuid.Uuid) : Result Bool :=
  ok (decide (self.bytes = other.bytes))

/-- [uuid::parser::{uuid::Uuid}::try_parse]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/uuid-1.23.4/src/parser.rs', lines 110:4-110:62
    Name pattern: [uuid::parser::{uuid::Uuid}::try_parse]
    Visibility: public -/
@[rust_fun "uuid::parser::{uuid::Uuid}::try_parse"]
axiom uuid.parser.Uuid.try_parse
  : Str → Result (core.result.Result uuid.Uuid uuid.error.Error)

/-- [x25519_dalek::x25519::{impl core::convert::From<[u8; 32usize]> for x25519_dalek::x25519::StaticSecret}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/x25519-dalek-3.0.0/src/x25519.rs', lines 249:4-249:44
    Name pattern: [x25519_dalek::x25519::{core::convert::From<x25519_dalek::x25519::StaticSecret, [u8; 32]>}::from]
    Visibility: public -/
@[rust_fun
  "x25519_dalek::x25519::{core::convert::From<x25519_dalek::x25519::StaticSecret, [u8; 32]>}::from"]
axiom x25519_dalek.x25519.StaticSecret.Insts.CoreConvertFromArrayU832.from
  : Array Std.U8 32#usize → Result x25519_dalek.x25519.StaticSecret

/-- [x25519_dalek::x25519::{x25519_dalek::x25519::StaticSecret}::to_bytes]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/x25519-dalek-3.0.0/src/x25519.rs', lines 235:4-235:38
    Name pattern: [x25519_dalek::x25519::{x25519_dalek::x25519::StaticSecret}::to_bytes]
    Visibility: public -/
@[rust_fun
  "x25519_dalek::x25519::{x25519_dalek::x25519::StaticSecret}::to_bytes"]
axiom x25519_dalek.x25519.StaticSecret.to_bytes
  : x25519_dalek.x25519.StaticSecret → Result (Array Std.U8 32#usize)

/-- [x25519_dalek::x25519::{impl core::convert::From<&'a x25519_dalek::x25519::StaticSecret> for x25519_dalek::x25519::PublicKey}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/x25519-dalek-3.0.0/src/x25519.rs', lines 257:4-257:50
    Name pattern: [x25519_dalek::x25519::{core::convert::From<x25519_dalek::x25519::PublicKey, &'a x25519_dalek::x25519::StaticSecret>}::from]
    Visibility: public -/
@[rust_fun
  "x25519_dalek::x25519::{core::convert::From<x25519_dalek::x25519::PublicKey, &'a x25519_dalek::x25519::StaticSecret>}::from"]
axiom
  x25519_dalek.x25519.PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from
  : x25519_dalek.x25519.StaticSecret → Result x25519_dalek.x25519.PublicKey

/-- [x25519_dalek::x25519::{x25519_dalek::x25519::PublicKey}::as_bytes]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/x25519-dalek-3.0.0/src/x25519.rs', lines 50:4-50:39
    Name pattern: [x25519_dalek::x25519::{x25519_dalek::x25519::PublicKey}::as_bytes]
    Visibility: public -/
@[rust_fun "x25519_dalek::x25519::{x25519_dalek::x25519::PublicKey}::as_bytes"]
axiom x25519_dalek.x25519.PublicKey.as_bytes
  : x25519_dalek.x25519.PublicKey → Result (Array Std.U8 32#usize)

/-- [libsignal_core::curve::log_public_key_trailing_bytes]:
    Source: 'rust/core/src/curve.rs', lines 566:0-568:1 -/
-- Logging affects neither the key nor the result.
def curve.log_public_key_trailing_bytes (_trailing : Std.Usize) : Result Unit :=
  ok ()

/-- [libsignal_core::curve::{libsignal_core::curve::PublicKey}::verify_signature_for_multipart_message]:
    Source: 'rust/core/src/curve.rs', lines 138:4-151:5
    Visibility: public -/
axiom curve.PublicKey.verify_signature_for_multipart_message
  : curve.PublicKey → Slice (Slice Std.U8) → Slice Std.U8 → Result Bool

/-- [libsignal_core::curve::{libsignal_core::curve::PublicKey}::is_torsion_free]:
    Source: 'rust/core/src/curve.rs', lines 165:4-174:5 -/
axiom curve.PublicKey.is_torsion_free : curve.PublicKey → Result Bool

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
