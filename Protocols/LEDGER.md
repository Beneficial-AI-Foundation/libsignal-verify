# Ledger

Axiom closures of the endpoint declarations and the list of admitted lemmas in the `Protocols`
library, regenerated whenever the library changes. The commands are at the end.

## State

| Item | Value |
| --- | --- |
| Date | 2026-10-28 |
| Lean | v4.31.0 |
| Mathlib | fabf563a (v4.31.0) |
| VCVio | cbd4144b |
| Aeneas | nightly-2026.09.30-0855ce1 |
| `sorry` under `Protocols/` | 10 |
| `sorry` under `ProtocolsTest/` | 0 |
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
not endpoints of the abstract model above, and `scripts/Ledger.lean` does not print them. The closures below come
from `#print axioms` on each declaration after `lake build`.

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

## How to regenerate

From the repository root, after `lake build`:

```
rg -n -g '*.lean' 'sorry|axiom|native_decide|set_option' Protocols Protocols.lean ProtocolsTest ProtocolsTest.lean
lake env lean scripts/Ledger.lean
```

The first command lists the admissions, the second prints the closures.
