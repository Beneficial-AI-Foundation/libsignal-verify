# Ledger

The admitted lemmas, stubs, contracts and pins of the `Protocols` library. CI checks the pins and
the admission counts of the State table. The command is at the end.

## State

| Item | Value |
| --- | --- |
| Date | 2026-11-11 |
| Lean | v4.35.0 |
| Mathlib | 56a00585 (v4.35.0) |
| VCVio | 88efe971 |
| Aeneas | nightly-2026.10.30-de16f3c |
| `sorry` or `sorryAx` under `Protocols/` | 14 |
| `sorry` or `sorryAx` under `ProtocolsTest/` | 0 |
| `axiom`, `native_decide`, `set_option` under `Protocols/` and `ProtocolsTest/` | 0 |

## Axiom closures

This ledger does not record axiom closures. A `#guard_msgs` check on `#print axioms` freezes each
closure, and `lake build` fails when one changes. The checks are in:

- `Protocols/Specs/Models/PQXDH.lean`: the six endpoint theorems of the abstract model and its
  security hops;
- `Protocols/Specs/PQXDH.lean`: the key-derivation mirror and the statements of the Full realization;
- `rust/Libsignal/Specs/Protocol/Pqxdh.lean`: the extracted `pqxdh_initiate` and `pqxdh_accept`;
- `ProtocolsTest/PQXDH/FaultFixtures.lean`: the three fault fixtures `alwaysPanic_fails`,
  `alwaysError_fails` and `alwaysDiverge_fails`. The file has no summary, and its checks are at its end;
- `ProtocolsTest/ToVCVio/CryptoFoundations/AEADAxioms.lean`: the twelve lemmas listed under "AEAD lemmas"
  below.

The `sorryAx` in the closures of the two security theorems of the abstract model comes from the five
admitted hops below, which are the only admitted declarations these theorems depend on. The four AEAD
lemmas that their imports reach are proved; see "AEAD lemmas" below. The `sorryAx` in the closures of the
Full realization statements comes from the stubs under "Security placeholders" and "Temporary stubs".

## AEAD lemmas

The four integrity lemmas of `Protocols/ToVCVio/CryptoFoundations/AEAD.lean`, repaired and proved
(#31, #32, #33), with the two advantage equalities and the six query-bound lemmas of their reductions.
No PQXDH theorem uses them: both security theorems assume a bound on `INT_CTXT_D_Advantage` directly.

The twelve lemmas are `AEAD.INT_CTXT_Advantage_le_INT_CTXT_VF_Advantage`,
`INT_CTXT_VF_Advantage_le_mul_INT_CTXT_Advantage`, `INT_CTXT_Advantage_le_INT_CTXT_D_Advantage`,
`INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage`, `INT_CTXT_VF_Advantage_ctxtToVf`,
`INT_CTXT_D_Advantage_ctxtToDec`, `ctxtToVf_encBound`, `ctxtToVf_vfBound`, `ctxtToDec_encBound`,
`ctxtToDec_decBound`, `vfToCtxt_encBound` and `decToCtxt_encBound`. The closure of each is `propext`,
`Classical.choice`, `Quot.sound`. `ProtocolsTest/ToVCVio/CryptoFoundations/AEADAxioms.lean` freezes these
closures.

## Admitted lemmas

| Lemma | File | Used by | Tracked in |
| --- | --- | --- | --- |
| `Protocols.Models.PQXDH.sigForgeProb_le_sig` | `Protocols/Models/PQXDH/UAKE/SecurityLemmas/SharedHops.lean` | both security theorems, hop 3 | PQXDH-model |
| `Protocols.Models.PQXDH.forgeHonestGoodProb_le_gap` | `Protocols/Models/PQXDH/UAKE/SecurityLemmas/DHHops.lean` | `uakeInitiator_secure_dh`, hop 5 | PQXDH-model after the KDF ruling, and this repository for the statement repair |
| `Protocols.Models.PQXDH.indistAdvantage_le_gap` | `Protocols/Models/PQXDH/UAKE/SecurityLemmas/DHHops.lean` | `uakeInitiator_secure_dh`, hop 6 | PQXDH-model after the KDF ruling |
| `Protocols.Models.PQXDH.forgeHonestGoodProb_le_pq` | `Protocols/Models/PQXDH/UAKE/SecurityLemmas/PQHops.lean` | `uakeInitiator_secure_pq`, hop 5 | discharge untracked, this repository for the statement repair |
| `Protocols.Models.PQXDH.indistAdvantage_le_pq` | `Protocols/Models/PQXDH/UAKE/SecurityLemmas/PQHops.lean` | `uakeInitiator_secure_pq`, hop 6 | discharge untracked |

The issue trackers of Beneficial-AI-Foundation/PQXDH-model and of this repository hold the items. The gaps
in the statements themselves, inherited from PQXDH-model, carry the label `deferred-fix` here.

## Security placeholders

These statements of the Full realization are stubs by design, apart from the admitted hops above. All are in
`Protocols/PQXDH/Security.lean`.

| Statement | Content | Premises beyond the contracts | Status |
| --- | --- | --- | --- |
| `Protocols.PQXDH.uakeInitiator_secure_dh` | advantage ≤ `εsig + 2q(εodh + 2εaead) + 3q²εpk` + `Pr[⊥]` | joint unforgeability of the identity key, the PQXDH oracle Diffie-Hellman assumption on the extracted X25519 and key derivation (an adaptation of mmPRF-ODH, assumed separately; the paper's random-oracle proof under ClawStDH and GapDH does not cover it), AEAD integrity, Kyber public-key guessing | stub |
| `Protocols.PQXDH.uakeInitiator_secure_pq` | advantage ≤ `εsig + 2q(εkem + εaead + εkdf) + 3q²εpk` + `Pr[⊥]` | as above without Diffie-Hellman, with IND-CCA of an abstract KEM and the Kyber bridge contract, KDF as a PRF keyed by the Kyber secret | stub |
| `Protocols.PQXDH.fullExp_noLostMass` | the Full experiment faults with probability 0 | the total contracts, RNG totality on the coin domain, Kyber1024-shaped honest Kyber pairs, an adversary sending only messages that fit in memory | stub |

The corollaries `uakeInitiator_secure_dh_total` and `uakeInitiator_secure_pq_total` are proved from these and
need no stub of their own.

## Temporary stubs

The stubs of these statements are temporary, unlike the security placeholders above.

| Statement | File | Content | Status |
| --- | --- | --- | --- |
| `Protocols.PQXDH.coreCompletion_extracted` | `Correctness.lean` | both extracted entry points return their keys with probability 1 | stub |
| `Protocols.PQXDH.jointKeyAgreement_extracted` | `Correctness.lean` | equal joint key records, chain index 0, with probability ≥ 1 − δ | stub |
| `Protocols.PQXDH.wrapperAgreement_uakeInitiator` | `Correctness.lean` | both parties output equal keys, with probability ≥ 1 − δ | stub |
| `Protocols.PQXDH.wrapperAgreement_uakeRecipient` | `Correctness.lean` | the same, in the correctness-only direction | stub |
| `Protocols.PQXDH.initiate_kdfInput_witness` | `Witness.lean` | a successful `pqxdh_initiate` derives its keys from its own key material | stub |
| `Protocols.PQXDH.accept_kdfInput_witness` | `Witness.lean` | the same for `pqxdh_accept` | stub |

## Contracts, policies and modelling choices of the Full realization

These are the hypotheses of the Full statements, each a named proposition. A contract describes an opaque
leaf of the extraction and is trusted. A policy describes what the calling application supplies. A modelling
choice describes something outside the extracted code. The contracts are in
`Protocols/PQXDH/Contracts.lean`, with fault-or-value forms in `PartialContracts`.

| Item | Kind | Describes | Discharged by |
| --- | --- | --- | --- |
| `AgreementDerived`, `AgreementTotal` | contract | `calculate_agreement`: commutation and success on derived keys; 32 bytes or `InvalidKeyAgreement` | curve25519-dalek-fork |
| `TorsionFreeTotal`, `DerivedCanonical` | contract | `is_torsion_free`; derived keys pass `is_canonical` | curve25519-dalek-fork |
| `SignTotal`, `SignVerify`, `VerifyTotal` | contract | XEdDSA signing and verification on the single identity key | curve25519-dalek-fork |
| `KyberEncapsBadLength`, `KyberEncapsBackend`, `KyberDecaps` | contract | the Kyber1024 backend: length branches, backend panic freedom and termination (libcrux's unbounded sampling loop) | a model of libcrux |
| `RngTotal` | contract | totality of the caller's generator on a domain containing the drawn states | the caller's choice of generator |
| `ToOwnedTotal` | contract | `str::to_owned` terminates; `pqxdh_accept` calls it only to build the error message for a non-canonical ephemeral key | none: the Aeneas standard library models no way to build a `String` from a `str`, so no translation patch can route the call through a modelled one |
| `HkdfSha256Contract` | contract | `crypto.hkdf_sha256` computes RFC 5869 from the MAC interface `H` | unchanged from `main` |
| `KyberBridge` | contract | extracted Kyber calls fault or return the outputs of an abstract KEM `K` | a model of libcrux |
| `KyberDeltaCorrect` | contract | correctness error of the extracted Kyber operations at most `δ` | published Kyber analysis with a model of libcrux |
| `ECKeyPairValid` on `P.ecKeygen` | policy | key pairs from the ideal generator have derived public halves | a correspondence with production key generation |
| `PQKeyPairShape` on `P.pqKeygen` | policy | Kyber pairs have the Kyber1024 type and lengths | a correspondence with production key generation |
| `Adversary.SendsFittingMessages` | policy | no message carries a Kyber key of `usize::MAX` bytes, which Rust cannot allocate | none needed |
| `P.coins` | modelling choice | one ideal draw of the generator state per session | a correspondence with production's generator |
| `P.ecKeygen`, `P.pqKeygen` | modelling choice | ideal key draws in place of `KeyPair::generate` on the caller's generator; their law is related neither to production's clamped generation nor to the abstract uniform exponent (see "Full EC key generation and abstract-generator relation" below) | a correspondence with production key generation |
| `syntheticAeadRoles`, `P.aead` | modelling choice | the synthetic UAKE/AEAD wrapper and its key roles; production has no such ciphertexts | a correspondence with production's first message |

## Modelling choices of the abstract model

Choices of the abstract model in `Protocols/Models/PQXDH/` that the theorems above rest on. None of them is
an admission.

| Item | Kind | Describes | Status |
| --- | --- | --- | --- |
| Single identity key, `Parameters.sig` | modelling choice | Bob's identity key pair signs his pre-keys and takes part in Diffie-Hellman, as in production; the signature scheme `Parameters.sig` draws its keys with `dhKeygen`, so completeness and unforgeability of `P.sig` refer to Diffie-Hellman identity keys | matches production's key use |
| Full EC key generation and abstract-generator relation | open bridge obligation | the abstract model draws identity, signed and one-time keys with `dhKeygen`, a uniform exponent; the Full realization draws with `P.ecKeygen`, whose law, public/private relation (`ECKeyPairValid`), clamping and generator assumption are separate. The relation between the two generators is not established, and results proved on the uniform exponent are not transferred to production | open |

## How to check

From the repository root:

```
rg -n -g '*.lean' 'sorry|axiom|native_decide|set_option' Protocols Protocols.lean ProtocolsTest ProtocolsTest.lean > admissions.log
python3 scripts/ledger-check.py admissions.log
```

The first command lists the candidate lines for admissions. `scripts/ledger-check.py` counts an admission on a
listed line when the line's executable text, with the comments of its file blanked, contains `sorry` or
`sorryAx` as a word, `axiom` as a declaration keyword (after optional attributes and modifiers), or
`native_decide` or `set_option`. So an explicit `sorryAx` term counts. The `sorryAx` in an axiom list that
`#guard_msgs` records in a doc comment does not count, and neither do the `#print axioms` commands of the spec
summaries. The scanner keeps string and character literals and quoted identifiers `«…»`, so a comment marker
inside one opens no comment. The script also compares the pins in the State table with `lean-toolchain` and
`lake-manifest.json`. `python3 scripts/ledger-check.py --self-test`, which CI runs first, checks the scanner on
fixed cases.
