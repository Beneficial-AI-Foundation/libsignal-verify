/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Jin Xing Lim
-/

import Protocols.ToVCVio.CryptoFoundations.AEAD
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Party
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Runtime
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Transcript
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Transport
import Protocols.ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import Protocols.ToVCVio.CryptoFoundations.SignatureAlg
import Protocols.ToVCVio.OracleComp.QueryTracking.Structures

/-! # Material staged for VCVio

Definitions and lemmas written for the PQXDH model that belong in VCVio rather than here:
the UAKE notion of Dodis and Fiore 2017 with its transport along party simulations, AEAD
games, strong unforgeability for signatures, nominal and gap Diffie-Hellman, and a query-log
helper. The files keep the module paths and namespaces of PQXDH-model at f862593, minus its
`ToVCVio` root. VCVio's open PR #476 carries the UAKE files on the Lean module system and the
measure-only probability API, neither available at the pinned VCVio; re-sync when the pin
advances. `UAKE/Runtime.lean` and `Scheme.Admissible` restate that PR's admissibility
conditions on the pinned API. The honest run and `Scheme.WellFormed` also contain fixes
that the PR does not have: a party is never stepped after it finishes, and outputs are
pure. -/
