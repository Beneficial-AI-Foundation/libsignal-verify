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
| `Protocols/ToMathlib.lean` | `PQXDH/ToMathlib.lean` | header rewritten, module docstring added |
| `Protocols/ToVCVio/CryptoFoundations/AEAD.lean` | `ToVCVio/CryptoFoundations/AEAD.lean` | header rewritten, docstrings added to the four admitted lemmas |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Defs.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/Defs.lean` | header rewritten, import paths, `Scheme.WellFormed` requires pure outputs, admissibility definitions from VCVio PR #476 added (see below) |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Party.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/Party.lean` | header rewritten, `runHonestLoop` never steps a party after it reports `done = true`, `Party.PureOutput` added |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Transcript.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/Transcript.lean` | header rewritten |
| `ProtocolsTest/ToVCVio/CryptoFoundations/AKE/UAKE/TranscriptFixtures.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/TranscriptFixtures.lean` | header rewritten, import path |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Transport.lean` | `PQXDH/AKE/UAKE/Transport.lean` | header rewritten, import path, one `beta_reduce` that does nothing on Lean 4.31 removed, `runHonestLoop_transport` generalised over the finished-sender flag |
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
