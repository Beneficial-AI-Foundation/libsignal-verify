# Ledger

Axiom closures of the endpoint declarations and the list of admitted lemmas in the `Protocols`
library, regenerated whenever the library changes. The commands are at the end.

## State

| Item | Value |
| --- | --- |
| Date | 2026-10-30 |
| Lean | v4.31.0 |
| Mathlib | fabf563a (v4.31.0) |
| VCVio | cbd4144b |
| Aeneas | nightly-2026.09.30-0855ce1 |
| `sorry` or `sorryAx` under `Protocols/` | 19 |
| `sorry` or `sorryAx` under `ProtocolsTest/` | 0 |
| `axiom`, `native_decide`, `set_option` under `Protocols/` and `ProtocolsTest/` | 0 |

## Endpoint closures

Model theorems, all in `Protocols/PQXDH/Model/UAKE/`.

| Declaration | File | Axioms |
| --- | --- | --- |
| `Protocols.PQXDH.uakeInitiator_perfectlyCorrect` | `Correctness.lean` | `propext`, `Classical.choice`, `Quot.sound` |
| `Protocols.PQXDH.uakeRecipient_perfectlyCorrect` | `Correctness.lean` | `propext`, `Classical.choice`, `Quot.sound` |
| `Protocols.PQXDH.uakeInitiator_wellFormed` | `WellFormed.lean` | `propext`, `Classical.choice`, `Quot.sound` |
| `Protocols.PQXDH.uakeRecipient_wellFormed` | `WellFormed.lean` | `propext`, `Classical.choice`, `Quot.sound` |
| `Protocols.PQXDH.uakeInitiator_secure_dh` | `Security.lean` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` |
| `Protocols.PQXDH.uakeInitiator_secure_pq` | `Security.lean` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` |

The `sorryAx` of the two security theorems comes from the six admitted hops below. Their closures contain no
axiom beyond `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`, and the hops are the only admitted
declarations they depend on. Their imports also reach the four AEAD admissions, which no theorem uses.

Extracted functions, in `rust/Libsignal/Translated/Protocol/Funs.lean`. These are the current axiom
dependencies of the two function declarations. Each theorem about them needs its own audit of its closure and
of its explicit hypotheses, including primitive contracts and correspondence assumptions. The lists contain
the logical axioms of Lean, opaque primitives and backend items of the extraction, and the native-decision
axiom that the extraction of `pqxdh_accept` introduces.

`libsignal_protocol.pqxdh.pqxdh_initiate`:

```
propext, Classical.choice, Quot.sound, crypto.hkdf_sha256, curve.PrivateKey.calculate_agreement, alloc.vec.Vec.into_boxed_slice, core.num.niche_types.NonZeroU8Inner, core.num.nonzero.NonZero, Aeneas.Std.core.fmt.Formatter, kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length, kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate
```

`libsignal_protocol.pqxdh.pqxdh_accept`:

```
propext, Classical.choice, Quot.sound, crypto.hkdf_sha256, curve.PrivateKey.calculate_agreement, curve.PublicKey.is_torsion_free, BoxSlice.Insts.CoreConvertFromShared0Slice.from, Slice.Insts.CoreCmpPartialEqArray.eq, Str.Insts.AllocBorrowToOwnedString.to_owned, core.num.niche_types.NonZeroU8Inner, core.num.nonzero.NonZero, Aeneas.Std.core.fmt.Formatter, kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length, kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate, libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1
```

## Realization closures

Declarations in `Protocols/PQXDH/Realization/`, which mirror the key derivation of the extracted code. They are
not endpoints of the abstract model above. `scripts/Ledger.lean` prints their closures after the endpoint
closures.

| Declaration | File | Axioms |
| --- | --- | --- |
| `Protocols.PQXDH.Realization.deriveKeysTotal` | `Kdf.lean` | `propext`, `Classical.choice`, `Quot.sound`, `crypto.hkdf_sha256`, `Aeneas.Std.core.fmt.Formatter` |
| `Protocols.PQXDH.Realization.deriveHK`, `deriveKeys`, `DeriveKeysTotal` | `Kdf.lean` | `propext`, `Classical.choice`, `Quot.sound`, `crypto.hkdf_sha256`, `Aeneas.Std.core.fmt.Formatter` |
| `Protocols.PQXDH.Realization.kdfInput`, `pubSlice`, `sliceOfKey`, `pubBytes` | `Kdf.lean` | `propext`, `Classical.choice`, `Quot.sound` |
| `Protocols.PQXDH.Realization.ECPub`, `Key`, `HandshakeKeys`, `rootKeyBytes`, `chainKeyBytes`, `pqrKeyBytes` | `Defs.lean` | `propext`, `Classical.choice`, `Quot.sound` |
| `Protocols.PQXDH.Realization.Bytes` | `Defs.lean` | none |

The only explicit premise of `deriveKeysTotal` is `HkdfSha256Contract H`, for a MAC interface `H`. Under it,
`deriveHK` succeeds on all public keys `dh1 dh2 dh3`, with or without the fourth DH output `dh4`, and on every
32-byte shared secret `ss`. The theorem proves totality of the Lean mirror of the KDF step, through
`HandshakeKeys.derive_spec` and `extend_from_slice_spec`. It does not prove that the mirror agrees with the KDF
input that the extracted `pqxdh_initiate` and `pqxdh_accept` build, and it says nothing about the values of the
derived keys.

`crypto.hkdf_sha256` and `Aeneas.Std.core.fmt.Formatter` are opaque primitives of the extraction on which
`HandshakeKeys.derive_spec` already depends; the theorem adds no axiom of its own. The closures contain no
`sorryAx`, no native-decision axiom, and no curve, KEM or randomness constant.

## Full realization closures

The correctness and security statements of the Full realization, in `Protocols/PQXDH/Realization/`, and the
fault fixtures in `ProtocolsTest/PQXDH/Realization/FaultFixtures.lean`. Their statements are frozen, with
these closures, by `Protocols/Specs/PQXDH/Realization.lean` and by the checks at the end of the fixture file.
The closures list the opaque leaves that the definitions of the Full scheme mention; what each statement
assumes about them is the explicit contract premises listed under "Contracts" below. The `sorryAx` comes
from the stubs listed under "Security placeholders" and "Temporary stubs". The fixtures are proved and depend
on no `sorryAx`.

| Declaration | File | Axioms |
| --- | --- | --- |
| `Protocols.PQXDH.Realization.uakeInitiator_secure_dh`, `uakeInitiator_secure_dh_total`, `uakeInitiator_secure_pq`, `uakeInitiator_secure_pq_total`, `fullExp_noLostMass`, `wrapperAgreement_uakeInitiator`, `wrapperAgreement_uakeRecipient` | `Security.lean`, `Correctness.lean` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, `crypto.hkdf_sha256`, `curve.PrivateKey.calculate_agreement`, `curve.PrivateKey.calculate_signature`, `curve.PrivateKey.public_key`, `curve.PublicKey.is_torsion_free`, `curve.PublicKey.verify_signature_for_multipart_message`, `BoxSlice.Insts.CoreConvertFromShared0Slice.from`, `Slice.Insts.CoreCmpPartialEqArray.eq`, `Str.Insts.AllocBorrowToOwnedString.to_owned`, `alloc.vec.Vec.into_boxed_slice`, `core.num.niche_types.NonZeroU8Inner`, `core.num.nonzero.NonZero`, `Aeneas.Std.core.fmt.Formatter`, `kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length`, `kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length`, `kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate`, `kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate`, `libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1` |
| `Protocols.PQXDH.Realization.coreCompletion_extracted`, `jointKeyAgreement_extracted` | `Correctness.lean` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, `crypto.hkdf_sha256`, `curve.PrivateKey.calculate_agreement`, `curve.PrivateKey.public_key`, `curve.PublicKey.is_torsion_free`, `BoxSlice.Insts.CoreConvertFromShared0Slice.from`, `Slice.Insts.CoreCmpPartialEqArray.eq`, `Str.Insts.AllocBorrowToOwnedString.to_owned`, `alloc.vec.Vec.into_boxed_slice`, `core.num.niche_types.NonZeroU8Inner`, `core.num.nonzero.NonZero`, `Aeneas.Std.core.fmt.Formatter`, `kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length`, `kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length`, `kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate`, `kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate`, `libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1` |
| `Protocols.PQXDH.Realization.initiate_kdfInput_witness` | `Witness.lean` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, `crypto.hkdf_sha256`, `curve.PrivateKey.calculate_agreement`, `alloc.vec.Vec.into_boxed_slice`, `core.num.niche_types.NonZeroU8Inner`, `core.num.nonzero.NonZero`, `Aeneas.Std.core.fmt.Formatter`, `kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length`, `kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate` |
| `Protocols.PQXDH.Realization.accept_kdfInput_witness` | `Witness.lean` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, `crypto.hkdf_sha256`, `curve.PrivateKey.calculate_agreement`, `curve.PublicKey.is_torsion_free`, `BoxSlice.Insts.CoreConvertFromShared0Slice.from`, `Slice.Insts.CoreCmpPartialEqArray.eq`, `Str.Insts.AllocBorrowToOwnedString.to_owned`, `core.num.niche_types.NonZeroU8Inner`, `core.num.nonzero.NonZero`, `Aeneas.Std.core.fmt.Formatter`, `kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length`, `kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate`, `libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1` |
| `Protocols.PQXDH.Realization.alwaysPanic_fails`, `alwaysError_fails`, `alwaysDiverge_fails` | `FaultFixtures.lean` | `propext`, `Classical.choice`, `Quot.sound`, `curve.PrivateKey.calculate_signature`, `curve.PublicKey.verify_signature_for_multipart_message`, `alloc.vec.Vec.into_boxed_slice`, `core.num.niche_types.NonZeroU8Inner`, `core.num.nonzero.NonZero`, `kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length` |

## Admitted lemmas

| Lemma | File | Used by | Tracked in |
| --- | --- | --- | --- |
| `AEAD.INT_CTXT_Advantage_le_INT_CTXT_VF_Advantage` | `Protocols/ToVCVio/CryptoFoundations/AEAD.lean` | no theorem (both security theorems assume a bound on `INT_CTXT_D_Advantage` directly) | PQXDH-model, and this repository for the statement gaps |
| `AEAD.INT_CTXT_VF_Advantage_le_mul_INT_CTXT_Advantage` | `Protocols/ToVCVio/CryptoFoundations/AEAD.lean` | no theorem (both security theorems assume a bound on `INT_CTXT_D_Advantage` directly) | PQXDH-model, and this repository for the statement gaps |
| `AEAD.INT_CTXT_Advantage_le_INT_CTXT_D_Advantage` | `Protocols/ToVCVio/CryptoFoundations/AEAD.lean` | no theorem (both security theorems assume a bound on `INT_CTXT_D_Advantage` directly) | PQXDH-model, and this repository for the statement gaps |
| `AEAD.INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage` | `Protocols/ToVCVio/CryptoFoundations/AEAD.lean` | no theorem (both security theorems assume a bound on `INT_CTXT_D_Advantage` directly) | PQXDH-model, and this repository for the statement gaps |
| `Protocols.PQXDH.sigForgeProb_le_sig` | `Protocols/PQXDH/Model/UAKE/SecurityLemmas/SharedHops.lean` | both security theorems, hop 3 | PQXDH-model |
| `Protocols.PQXDH.pqpkGuessedProb_le` | `Protocols/PQXDH/Model/UAKE/SecurityLemmas/SharedHops.lean` | both security theorems, hop 4 | PQXDH-model |
| `Protocols.PQXDH.forgeHonestGoodProb_le_gap` | `Protocols/PQXDH/Model/UAKE/SecurityLemmas/DHHops.lean` | `uakeInitiator_secure_dh`, hop 5 | PQXDH-model after the KDF ruling, and this repository for the statement repair |
| `Protocols.PQXDH.indistAdvantage_le_gap` | `Protocols/PQXDH/Model/UAKE/SecurityLemmas/DHHops.lean` | `uakeInitiator_secure_dh`, hop 6 | PQXDH-model after the KDF ruling |
| `Protocols.PQXDH.forgeHonestGoodProb_le_pq` | `Protocols/PQXDH/Model/UAKE/SecurityLemmas/PQHops.lean` | `uakeInitiator_secure_pq`, hop 5 | discharge untracked, this repository for the statement repair |
| `Protocols.PQXDH.indistAdvantage_le_pq` | `Protocols/PQXDH/Model/UAKE/SecurityLemmas/PQHops.lean` | `uakeInitiator_secure_pq`, hop 6 | discharge untracked |

The issue trackers of Beneficial-AI-Foundation/PQXDH-model and of this repository hold the items. The gaps
in the statements themselves, inherited from PQXDH-model, carry the label `deferred-fix` here.

## Security placeholders

Statements of the Full realization whose proofs belong to the security milestone. They are stubs by design,
outside the count of admitted hops above. All are in `Protocols/PQXDH/Realization/Security.lean`.

| Statement | Content | Premises beyond the contracts | Status |
| --- | --- | --- | --- |
| `Protocols.PQXDH.Realization.uakeInitiator_secure_dh` | advantage ≤ `εsig + 2q(εodh + 2εaead) + 3q²εpk` + `Pr[⊥]` | joint unforgeability of the identity key, the PQXDH oracle Diffie-Hellman assumption on the extracted X25519 and key derivation (random-oracle model, strong Diffie-Hellman), AEAD integrity, Kyber public-key guessing | stub |
| `Protocols.PQXDH.Realization.uakeInitiator_secure_pq` | advantage ≤ `εsig + 2q(εkem + εaead + εkdf) + 3q²εpk` + `Pr[⊥]` | as above without Diffie-Hellman, with IND-CCA of an abstract KEM and the Kyber bridge contract, KDF as a PRF keyed by the Kyber secret | stub |
| `Protocols.PQXDH.Realization.fullExp_noLostMass` | the Full experiment faults with probability 0 | the total contracts, RNG totality on the coin domain, Kyber1024-shaped honest Kyber pairs, an adversary sending only messages that fit in memory | stub |

The corollaries `uakeInitiator_secure_dh_total` and `uakeInitiator_secure_pq_total` are proved from these and
need no stub of their own.

## Temporary stubs

Statements to be proved before the security statements. They are stubs only until their proofs land and are
not placeholders.

| Statement | File | Content | Status |
| --- | --- | --- | --- |
| `Protocols.PQXDH.Realization.coreCompletion_extracted` | `Correctness.lean` | both extracted entry points return their keys with probability 1 | stub |
| `Protocols.PQXDH.Realization.jointKeyAgreement_extracted` | `Correctness.lean` | equal joint key records, chain index 0, with probability ≥ 1 − δ | stub |
| `Protocols.PQXDH.Realization.wrapperAgreement_uakeInitiator` | `Correctness.lean` | both parties output equal keys, with probability ≥ 1 − δ | stub |
| `Protocols.PQXDH.Realization.wrapperAgreement_uakeRecipient` | `Correctness.lean` | the same, in the correctness-only direction | stub |
| `Protocols.PQXDH.Realization.initiate_kdfInput_witness` | `Witness.lean` | a successful `pqxdh_initiate` derives its keys from its own key material | stub |
| `Protocols.PQXDH.Realization.accept_kdfInput_witness` | `Witness.lean` | the same for `pqxdh_accept` | stub |

## Contracts, policies and modelling choices of the Full realization

Hypotheses of the Full statements, each a named proposition, never an axiom. A contract describes an opaque
leaf of the extraction and is trusted; a policy describes what the calling application supplies; a modelling
choice describes something outside the extracted code. The contracts are in
`Protocols/PQXDH/Realization/Contracts.lean`, with fault-or-value forms in `PartialContracts`.

| Item | Kind | Describes | Planned discharge |
| --- | --- | --- | --- |
| `AgreementDerived`, `AgreementTotal` | contract | `calculate_agreement`: commutation and success on derived keys; 32 bytes or `InvalidKeyAgreement` | curve25519-dalek-fork |
| `TorsionFreeTotal`, `DerivedCanonical` | contract | `is_torsion_free`; derived keys pass `is_canonical` | curve25519-dalek-fork |
| `SignTotal`, `SignVerify`, `VerifyTotal` | contract | XEdDSA signing and verification on the single identity key | curve25519-dalek-fork |
| `KyberEncapsBadLength`, `KyberEncapsBackend`, `KyberDecaps` | contract | the Kyber1024 backend: length branches, backend panic freedom and termination (libcrux's unbounded sampling loop) | a model of libcrux |
| `RngTotal` | contract | totality of the caller's generator on a domain containing the drawn states | the caller's choice of generator |
| `VecIntoBoxedSlice`, `BoxSliceFromU8`, `SliceEqArrayU8`, `ToOwnedTotal` | contract | standard-library conversions | short faithful bodies |
| `HkdfSha256Contract` | contract | `crypto.hkdf_sha256` computes RFC 5869 from the MAC interface `H` | existing contract |
| `KyberBridge` | contract | extracted Kyber calls fault or return the outputs of an abstract KEM `K` | a model of libcrux |
| `KyberDeltaCorrect` | contract | correctness error of the extracted Kyber operations at most `δ` | published Kyber analysis with a model of libcrux |
| `ECKeyPairValid` on `P.ecKeygen` | policy | key pairs from the ideal generator have derived public halves | the bridge to production key generation |
| `PQKeyPairShape` on `P.pqKeygen` | policy | Kyber pairs have the Kyber1024 type and lengths | the bridge to production key generation |
| `Adversary.SendsFittingMessages` | policy | no message carries a Kyber key of `usize::MAX` bytes, which Rust cannot allocate | — |
| `P.coins` | modelling choice | one ideal draw of the generator state per session | implementation milestone |
| `P.ecKeygen`, `P.pqKeygen` | modelling choice | ideal key draws, not `KeyPair::generate` on the caller's generator; their law is not related to production's clamped generation or to the abstract uniform exponent | open bridge obligation |
| `syntheticAeadRoles`, `P.aead` | modelling choice | the synthetic UAKE/AEAD wrapper and its key roles; production has no such ciphertexts | a route beyond the wrapper, at the security milestone |

## How to regenerate

From the repository root, after `lake build`:

```
rg -n -g '*.lean' 'sorry|axiom|native_decide|set_option' Protocols Protocols.lean ProtocolsTest ProtocolsTest.lean
lake env lean scripts/Ledger.lean
```

The first command lists the admissions, the second prints the endpoint, Realization and Full realization
closures. The first command only selects candidate lines; `scripts/ledger-check.py` counts an admission on a
listed line when the line's executable text, with the comments of its file blanked, contains `sorry` or
`sorryAx` as a word, `axiom` as a declaration keyword (after optional attributes and modifiers), or
`native_decide` or `set_option`. An explicit `sorryAx` term counts; the `sorryAx` in an axiom list recorded by
`#guard_msgs`, which is a doc comment, and the `#print axioms` commands of the spec summaries do not.
