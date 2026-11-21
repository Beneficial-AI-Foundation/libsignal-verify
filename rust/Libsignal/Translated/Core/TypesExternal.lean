-- [libsignal_core]: external types.
import Aeneas
import Libsignal.Translated.Shared
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.setOption false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-- [core::num::niche_types::NonZeroU64Inner]
    Source: '/rustc/library/core/src/num/niche_types.rs', lines 20:8-20:55
    Name pattern: [core::num::niche_types::NonZeroU64Inner]
    Visibility: public -/
@[rust_type "core::num::niche_types::NonZeroU64Inner"]
axiom core.num.niche_types.NonZeroU64Inner : Type

/-- [core::num::niche_types::NonZeroU8Inner]
    Source: '/rustc/library/core/src/num/niche_types.rs', lines 20:8-20:55
    Name pattern: [core::num::niche_types::NonZeroU8Inner]
    Visibility: public -/
@[rust_type "core::num::niche_types::NonZeroU8Inner"]
axiom core.num.niche_types.NonZeroU8Inner : Type

/-- [core::num::nonzero::NonZero]
    Source: '/rustc/library/core/src/num/nonzero.rs', lines 128:0-128:40
    Name pattern: [core::num::nonzero::NonZero]
    Visibility: public -/
@[rust_type "core::num::nonzero::NonZero"]
axiom core.num.nonzero.NonZero (T : Type) (Clause0_NonZeroInner : Type) : Type

/-- [uuid::error::Error]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/uuid-1.19.0/src/error.rs', lines 5:0-5:16
    Name pattern: [uuid::error::Error]
    Visibility: public -/
@[rust_type "uuid::error::Error"]
axiom uuid.error.Error : Type

/-- [x25519_dalek::x25519::PublicKey]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/x25519-dalek-3.0.0/src/x25519.rs', lines 32:0-32:20
    Name pattern: [x25519_dalek::x25519::PublicKey]
    Visibility: public -/
@[rust_type "x25519_dalek::x25519::PublicKey"]
axiom x25519_dalek.x25519.PublicKey : Type

/-- [x25519_dalek::x25519::StaticSecret]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/x25519-dalek-3.0.0/src/x25519.rs', lines 206:0-206:23
    Name pattern: [x25519_dalek::x25519::StaticSecret]
    Visibility: public -/
@[rust_type "x25519_dalek::x25519::StaticSecret"]
axiom x25519_dalek.x25519.StaticSecret : Type
