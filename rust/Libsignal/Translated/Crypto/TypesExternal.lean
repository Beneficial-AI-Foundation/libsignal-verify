-- [signal_crypto]: external types.
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

-- core::num::error::TryFromIntError is shared; imported from Libsignal.Translated.Shared.Core.

/-- [aes::autodetect::Aes256]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/aes-0.8.4/src/autodetect.rs', lines 52:8-55:9
    Name pattern: [aes::autodetect::Aes256]
    Visibility: public -/
@[rust_type "aes::autodetect::Aes256"]
axiom aes.autodetect.Aes256 : Type

/-- [typenum::uint::UInt]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/typenum-1.19.0/src/uint.rs', lines 148:0-148:21
    Name pattern: [typenum::uint::UInt]
    Visibility: public -/
@[rust_type "typenum::uint::UInt"]
axiom typenum.uint.UInt (U : Type) (B : Type) : Type

/-- [generic_array::GenericArrayImplOdd]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/generic-array-0.14.7/src/lib.rs', lines 148:0-148:36
    Name pattern: [generic_array::GenericArrayImplOdd]
    Visibility: public -/
@[rust_type "generic_array::GenericArrayImplOdd"]
axiom generic_array.GenericArrayImplOdd (T : Type) (U : Type) : Type

/-- [generic_array::GenericArrayImplEven]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/generic-array-0.14.7/src/lib.rs', lines 126:0-126:37
    Name pattern: [generic_array::GenericArrayImplEven]
    Visibility: public -/
@[rust_type "generic_array::GenericArrayImplEven"]
axiom generic_array.GenericArrayImplEven (T : Type) (U : Type) : Type

/-- [inout::inout::InOut]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/inout-0.1.4/src/inout.rs', lines 7:0-7:31
    Name pattern: [inout::inout::InOut]
    Visibility: public -/
@[rust_type "inout::inout::InOut" (mutRegions := #[1])]
axiom inout.inout.InOut (T : Type) : Type

/-- [generic_array::GenericArray]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/generic-array-0.14.7/src/lib.rs', lines 179:0-179:45
    Name pattern: [generic_array::GenericArray]
    Visibility: public -/
@[rust_type "generic_array::GenericArray"]
axiom generic_array.GenericArray (T : Type) (U : Type) (Clause0_ArrayType :
  Type) : Type

/-- [cipher::stream_wrapper::StreamCipherCoreWrapper]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/cipher-0.4.4/src/stream_wrapper.rs', lines 17:0-17:52
    Name pattern: [cipher::stream_wrapper::StreamCipherCoreWrapper]
    Visibility: public -/
@[rust_type "cipher::stream_wrapper::StreamCipherCoreWrapper"]
axiom cipher.stream_wrapper.StreamCipherCoreWrapper (T : Type)
  (Clause0_BlockSize : Type) (Clause0_Clause0_ArrayType : Type) (Clause1_Output
  : Type) : Type

/-- [ctr::ctr_core::CtrCore]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/ctr-0.9.2/src/ctr_core.rs', lines 13:0-13:24
    Name pattern: [ctr::ctr_core::CtrCore]
    Visibility: public -/
@[rust_type "ctr::ctr_core::CtrCore"]
axiom ctr.ctr_core.CtrCore (C : Type) (F : Type) (Clause0_Clause0_BlockSize :
  Type) (Clause0_Clause0_Clause0_ArrayType : Type) (Clause1_Clause0_BlockSize :
  Type) (Clause1_Clause0_Clause0_ArrayType : Type) (Clause2_CtrNonce : Type)
  (Clause2_Backend : Type) (Clause2_Clause0_ArrayType : Type)
  (Clause2_Clause2_Clause0_Error : Type) (Clause2_Clause2_Clause1_Error : Type)
  (Clause2_Clause2_Clause2_Error : Type) (Clause2_Clause2_Clause3_Error : Type)
  (Clause2_Clause2_Clause4_Error : Type) (Clause2_Clause2_Clause5_Error : Type)
  (Clause2_Clause2_Clause6_Error : Type) (Clause2_Clause2_Clause7_Error : Type)
  (Clause2_Clause2_Clause8_Error : Type) (Clause2_Clause2_Clause9_Error : Type)
  : Type

/-- [ctr::flavors::ctr32::CtrNonce32]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/ctr-0.9.2/src/flavors/ctr32.rs', lines 16:0-16:42
    Name pattern: [ctr::flavors::ctr32::CtrNonce32]
    Visibility: public -/
@[rust_type "ctr::flavors::ctr32::CtrNonce32"]
axiom ctr.flavors.ctr32.CtrNonce32 (N : Type) (Clause0_ArrayType : Type) : Type

/-- [ghash::GHash]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/ghash-0.5.1/src/lib.rs', lines 58:0-58:16
    Name pattern: [ghash::GHash]
    Visibility: public -/
@[rust_type "ghash::GHash"]
axiom ghash.GHash : Type

/-- [inout::inout_buf::InOutBuf]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/inout-0.1.4/src/inout_buf.rs', lines 11:0-11:34
    Name pattern: [inout::inout_buf::InOutBuf]
    Visibility: public -/
@[rust_type "inout::inout_buf::InOutBuf" (mutRegions := #[1])]
axiom inout.inout_buf.InOutBuf (T : Type) : Type

/-- [inout::reserved::InOutBufReserved]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/inout-0.1.4/src/reserved.rs', lines 17:0-17:42
    Name pattern: [inout::reserved::InOutBufReserved]
    Visibility: public -/
@[rust_type "inout::reserved::InOutBufReserved" (mutRegions := #[1])]
axiom inout.reserved.InOutBufReserved (T : Type) : Type

/-- [subtle::Choice]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 120:0-120:17
    Name pattern: [subtle::Choice]
    Visibility: public -/
@[rust_type "subtle::Choice"]
axiom subtle.Choice : Type

/-- [typenum::private::InvertedUInt]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/typenum-1.19.0/src/private.rs', lines 74:0-74:53
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
