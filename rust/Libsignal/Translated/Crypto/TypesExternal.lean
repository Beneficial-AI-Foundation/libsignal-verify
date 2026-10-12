-- [signal_crypto]: external types.
import Aeneas
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

/-- [aes::autodetect::Aes256]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/aes-0.9.1/src/autodetect.rs', lines 50:8-53:9
    Name pattern: [aes::autodetect::Aes256]
    Visibility: public -/
@[rust_type "aes::autodetect::Aes256"]
axiom aes.autodetect.Aes256 : Type

/-- [ghash::GHash]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/ghash-0.6.0/src/lib.rs', lines 35:0-35:16
    Name pattern: [ghash::GHash]
    Visibility: public -/
@[rust_type "ghash::GHash"]
axiom ghash.GHash : Type

/-- [subtle::Choice]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 120:0-120:17
    Name pattern: [subtle::Choice]
    Visibility: public -/
-- `subtle::Choice` is `struct Choice(u8)`, holding 0 or 1.
@[rust_type "subtle::Choice"]
structure subtle.Choice where
  val : Std.U8

-- (dropped axiom uuid.Uuid; provided by an imported sibling lib)

/-- [typenum::uint::UInt]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/typenum-1.20.1/src/uint.rs', lines 148:0-148:21
    Name pattern: [typenum::uint::UInt]
    Visibility: public -/
@[rust_type "typenum::uint::UInt"]
axiom typenum.uint.UInt (U : Type) (B : Type) : Type

/-- [typenum::private::InvertedUInt]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/typenum-1.20.1/src/private.rs', lines 74:0-74:53
    Name pattern: [typenum::private::InvertedUInt]
    Visibility: public -/
@[rust_type "typenum::private::InvertedUInt"]
axiom typenum.private.InvertedUInt (IU : Type) (B : Type) : Type

/-- [signal_crypto::aes_ctr::Aes256Ctr32]
    Source: 'rust/crypto/src/aes_ctr.rs', lines 16:0-18:1
    Visibility: public -/
axiom aes_ctr.Aes256Ctr32 : Type

/-- [signal_crypto::hash::CryptographicMac]
    Source: 'rust/crypto/src/hash.rs', lines 14:0-17:1
    Visibility: public -/
axiom hash.CryptographicMac : Type

/-- [signal_crypto::hash::CryptographicHash]
    Source: 'rust/crypto/src/hash.rs', lines 54:0-58:1
    Visibility: public -/
axiom hash.CryptographicHash : Type
