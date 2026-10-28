# Attribution

This repository is released under the GNU Affero General Public License 3.0, see `LICENSE` in the
project root. The files listed here were ported from other projects and keep their own licence.

## Galois Inc., libsignal-docs-and-models

- Source: <https://github.com/GaloisInc/libsignal-docs-and-models>, commit
  `f8625935808bff4a85f9a59f751dac81d03384ca`.
- Copyright (c) 2026 Galois Inc. Author Ben Hamlin.
- Licence: Apache License 2.0, text in `LICENSES/Apache-2.0.txt`.
- The source repository has no NOTICE file.

| File here | File there | Changes made here |
| --- | --- | --- |
| `Protocols/PQXDH/Model/Basic.lean` | `PQXDH/Spec/Basic.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, docstrings say "model" for the Lean side |
| `Protocols/PQXDH/Model/UAKE/Correctness.lean` | `PQXDH/Spec/UAKE/Correctness.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, docstrings say "model" for the Lean side |
| `Protocols/PQXDH/Model/UAKE/CorrectnessLemmas.lean` | `PQXDH/Spec/UAKE/CorrectnessLemmas.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, module docstring says "model", the proofs of `run_support_initiator` and `run_support_recipient` adapted to the finished-sender flag of `Party.runHonestLoop` |
| `Protocols/PQXDH/Model/UAKE/Defs.lean` | `PQXDH/Spec/UAKE/Defs.lean` | header rewritten, import paths, namespace `PQXDH` renamed `Protocols.PQXDH`, docstring path and paper link updated |
| `Protocols/PQXDH/Model/UAKE/Security.lean` | `PQXDH/Spec/UAKE/Security.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, docstrings say "model" for the Lean side |
| `Protocols/PQXDH/Model/UAKE/SecurityLemmas.lean` | `PQXDH/Spec/UAKE/SecurityLemmas.lean` | header rewritten, import paths, module docstring says "model", names the theorems with their new prefix and notes the transcript-binding gap of the forgery cores |
| `Protocols/PQXDH/Model/UAKE/SecurityLemmas/DHHops.lean` | `PQXDH/Spec/UAKE/SecurityLemmas/DHHops.lean` | header rewritten, import paths, namespace `PQXDH` renamed `Protocols.PQXDH`, theorem names in docstrings carry the new prefix, docstrings of the two admitted lemmas extended |
| `Protocols/PQXDH/Model/UAKE/SecurityLemmas/Games.lean` | `PQXDH/Spec/UAKE/SecurityLemmas/Games.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, the replay example in the docstring of `pqpkGuessed` qualified by the one-time key |
| `Protocols/PQXDH/Model/UAKE/SecurityLemmas/PQHops.lean` | `PQXDH/Spec/UAKE/SecurityLemmas/PQHops.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, theorem names in docstrings carry the new prefix, docstrings of the two admitted lemmas extended |
| `Protocols/PQXDH/Model/UAKE/SecurityLemmas/SharedHops.lean` | `PQXDH/Spec/UAKE/SecurityLemmas/SharedHops.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, docstrings of the two admitted lemmas extended |
| `Protocols/PQXDH/Model/UAKE/WellFormed.lean` | `PQXDH/Spec/UAKE/WellFormed.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, docstrings say "model" for the Lean side, two theorem docstrings that said "extracted" corrected, both proofs also discharge the pure-output conditions of `Scheme.WellFormed`, module and theorem docstrings name them |
| `Protocols/PQXDH/Model/UAKE/WellFormedLemmas.lean` | `PQXDH/Spec/UAKE/WellFormedLemmas.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, docstrings say "model" for the Lean side, four lemmas added stating that the model parties' output functions are pure, module docstring names them |
| `Protocols/PQXDH/Realization/Defs.lean` | `PQXDH/Aeneas/Full/UAKE/Defs.lean` (`Bytes`, `ECPub`, `Key`, `HandshakeKeys`, `rootKeyBytes`, `chainKeyBytes`, `pqrKeyBytes`, lines 68-71, 99-102, 220-227) | header rewritten, import paths, namespace `PQXDH.Aeneas.Full` renamed `Protocols.PQXDH.Realization`, module docstring added, only the seven declarations the KDF mirror uses are taken |
| `Protocols/PQXDH/Realization/Kdf.lean` | `PQXDH/Aeneas/Full/UAKE/SecurityDefs.lean` (`pubBytes`, `sliceOfKey`, `pubSlice`, `kdfInput`, `deriveHK`, `deriveKeys`, `DeriveKeysTotal`, lines 44-110) | header rewritten, import paths, namespace `PQXDH.Aeneas.Full` renamed `Protocols.PQXDH.Realization`, module docstring added, the source's `noncomputable section` replaced by `noncomputable` on `deriveHK` and `deriveKeys` only; theorem `deriveKeysTotal` is new here (not in the source): it proves `DeriveKeysTotal` from `HkdfSha256Contract` |
| `Protocols/ToMathlib.lean` | `PQXDH/ToMathlib.lean` | header rewritten, module docstring added |
| `Protocols/ToVCVio/CryptoFoundations/AEAD.lean` | `ToVCVio/CryptoFoundations/AEAD.lean` | header rewritten, docstrings added to the four admitted lemmas |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Defs.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/Defs.lean` | header rewritten, import paths, `Scheme.WellFormed` requires pure outputs, admissibility definitions from VCVio PR #476 added (see below) |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Party.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/Party.lean` | header rewritten, `runHonestLoop` never steps a party after it reports `done = true`, `Party.PureOutput` added |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Transcript.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/Transcript.lean` | header rewritten |
| `ProtocolsTest/ToVCVio/CryptoFoundations/AKE/UAKE/TranscriptFixtures.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/TranscriptFixtures.lean` | header rewritten, import path |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Transport.lean` | `PQXDH/AKE/UAKE/Transport.lean` | header rewritten, import path, one `beta_reduce` that does nothing on Lean 4.31 removed, `runHonestLoop_transport` generalised over the finished-sender flag, identity lemmas `InitResult.map_id`, `StepResult.map_id`, `Sim.refl` and `Adversary.transport_id` added (not in the source) |
| `Protocols/ToVCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean` | `ToVCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean` | header rewritten, namespace `PQXDH.DiffieHellman` renamed `DiffieHellman` |
| `Protocols/ToVCVio/CryptoFoundations/SignatureAlg.lean` | `ToVCVio/CryptoFoundations/SignatureAlg.lean` | header rewritten, import path |
| `Protocols/ToVCVio/OracleComp/QueryTracking/Structures.lean` | `ToVCVio/OracleComp/QueryTracking/Structures.lean` | header rewritten |

## Verified-zkEVM, VCVio pull request #476

- Source: <https://github.com/Verified-zkEVM/VCVio/pull/476>, head commit
  `17b53734961eca3c8b74caed864d92f8ce40e9aa`.
- Copyright (c) 2026 Galois Inc. Author Ben Hamlin (`Defs.lean`). Copyright (c) 2026 Devon
  Tuma (`Runtime.lean`).
- Licence: Apache License 2.0, text in `LICENSES/Apache-2.0.txt`.

| File here | File there | Changes made here |
| --- | --- | --- |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Defs.lean` | `VCVio/CryptoFoundations/AKE/UAKE/Defs.lean` | `HonestCompletionExp`, `Scheme.HonestlyCompletes` and `Scheme.Admissible` only, stated with `Pr[= · \| ·]` instead of measures, docstrings rewritten |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Runtime.lean` | `VCVio/CryptoFoundations/AKE/UAKE/Runtime.lean` | `RuntimeCoherent` stated for `SPMF` semantics and native `MonadLiftT` lifts instead of measures and `MonadAttach`, docstrings rewritten |
