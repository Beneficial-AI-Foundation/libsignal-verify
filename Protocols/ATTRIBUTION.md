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
| `Protocols/PQXDH/Model/UAKE/CorrectnessLemmas.lean` | `PQXDH/Spec/UAKE/CorrectnessLemmas.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, module docstring says "model" |
| `Protocols/PQXDH/Model/UAKE/Defs.lean` | `PQXDH/Spec/UAKE/Defs.lean` | header rewritten, import paths, namespace `PQXDH` renamed `Protocols.PQXDH`, docstring path and paper link updated |
| `Protocols/PQXDH/Model/UAKE/Security.lean` | `PQXDH/Spec/UAKE/Security.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, docstrings say "model" for the Lean side |
| `Protocols/PQXDH/Model/UAKE/SecurityLemmas.lean` | `PQXDH/Spec/UAKE/SecurityLemmas.lean` | header rewritten, import paths, module docstring says "model", names the theorems with their new prefix and notes the transcript-binding gap of the forgery cores |
| `Protocols/PQXDH/Model/UAKE/SecurityLemmas/DHHops.lean` | `PQXDH/Spec/UAKE/SecurityLemmas/DHHops.lean` | header rewritten, import paths, namespace `PQXDH` renamed `Protocols.PQXDH`, theorem names in docstrings carry the new prefix, docstrings of the two admitted lemmas extended |
| `Protocols/PQXDH/Model/UAKE/SecurityLemmas/Games.lean` | `PQXDH/Spec/UAKE/SecurityLemmas/Games.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, the replay example in the docstring of `pqpkGuessed` qualified by the one-time key |
| `Protocols/PQXDH/Model/UAKE/SecurityLemmas/PQHops.lean` | `PQXDH/Spec/UAKE/SecurityLemmas/PQHops.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, theorem names in docstrings carry the new prefix, docstrings of the two admitted lemmas extended |
| `Protocols/PQXDH/Model/UAKE/SecurityLemmas/SharedHops.lean` | `PQXDH/Spec/UAKE/SecurityLemmas/SharedHops.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, docstrings of the two admitted lemmas extended |
| `Protocols/PQXDH/Model/UAKE/WellFormed.lean` | `PQXDH/Spec/UAKE/WellFormed.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, docstrings say "model" for the Lean side, two theorem docstrings that said "extracted" corrected |
| `Protocols/PQXDH/Model/UAKE/WellFormedLemmas.lean` | `PQXDH/Spec/UAKE/WellFormedLemmas.lean` | header rewritten, import path, namespace `PQXDH` renamed `Protocols.PQXDH`, docstrings say "model" for the Lean side |
| `Protocols/ToMathlib.lean` | `PQXDH/ToMathlib.lean` | header rewritten, module docstring added |
| `Protocols/ToVCVio/CryptoFoundations/AEAD.lean` | `ToVCVio/CryptoFoundations/AEAD.lean` | header rewritten, docstrings added to the four admitted lemmas |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Defs.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/Defs.lean` | header rewritten, import paths |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Party.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/Party.lean` | header rewritten |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Transcript.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/Transcript.lean` | header rewritten |
| `ProtocolsTest/ToVCVio/CryptoFoundations/AKE/UAKE/TranscriptFixtures.lean` | `ToVCVio/CryptoFoundations/AKE/UAKE/TranscriptFixtures.lean` | header rewritten, import path |
| `Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/Transport.lean` | `PQXDH/AKE/UAKE/Transport.lean` | header rewritten, import path, one `beta_reduce` that does nothing on Lean 4.31 removed |
| `Protocols/ToVCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean` | `ToVCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean` | header rewritten, namespace `PQXDH.DiffieHellman` renamed `DiffieHellman` |
| `Protocols/ToVCVio/CryptoFoundations/SignatureAlg.lean` | `ToVCVio/CryptoFoundations/SignatureAlg.lean` | header rewritten, import path |
| `Protocols/ToVCVio/OracleComp/QueryTracking/Structures.lean` | `ToVCVio/OracleComp/QueryTracking/Structures.lean` | header rewritten |
