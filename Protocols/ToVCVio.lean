/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Jin Xing Lim
-/

import Protocols.ToVCVio.CryptoFoundations.AEAD
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.OracleInvariants
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Partnering
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Party
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Runtime
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Transcript
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Transport
import Protocols.ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import Protocols.ToVCVio.CryptoFoundations.JointSignatureAlg
import Protocols.ToVCVio.CryptoFoundations.KEMCorrectness
import Protocols.ToVCVio.EvalDist.Monad.Basic
import Protocols.ToVCVio.OracleComp.ProbComp
import Protocols.ToVCVio.OracleComp.QueryTracking.QueryBound
import Protocols.ToVCVio.OracleComp.QueryTracking.Structures

/-! # Material staged for VCVio

Definitions and lemmas written for the PQXDH model that belong in VCVio rather than here:
the UAKE notion of Dodis and Fiore 2017 with its transport along party simulations, AEAD
games, joint EUF-CMA for a signature key that also takes part in agreement, nominal and gap
Diffie-Hellman, and a query-log helper. The files keep the module paths and namespaces of
PQXDH-model at f862593, minus its `ToVCVio` root. Four files are new here and hold the generic
part of the hop-4 proof of the PQXDH model. Three follow VCVio's module paths:
`EvalDist/Monad/Basic`, `OracleComp/ProbComp` and `OracleComp/QueryTracking/QueryBound` hold
probability lemmas, among them a potential bound for bad events of simulated computations.
`CryptoFoundations/AKE/UAKE/OracleInvariants` holds facts about the UAKE oracle for every scheme.
The hop-4 proof uses all of these lemmas. It instantiates the potential bound with the UAKE
oracle, and it uses the nonempty result type of a `ProbComp` computation to show that a bound on a
key generator's outputs is nonnegative. `CryptoFoundations/JointSignatureAlg` is a fifth new file.
It holds the joint EUF-CMA game of the hop-3 premise. VCVio's PR #476 (merged 2026-10-20, merge
commit `abed2e31`) carries the UAKE
files on the Lean module system and the measure-only probability API, neither available at the
pinned VCVio. The UAKE source files are unchanged between the captured PR head `17b53734` and
the merge. The pin remains `cbd4144b`; advancing it requires a separate API migration.
`UAKE/Runtime.lean` and `Scheme.Admissible` restate runtime coherence and honest-path admission
on the pinned API; they do not ensure losslessness of adversarial executions in a monad with
failure. The honest run and `Scheme.WellFormed` also contain fixes
that the PR does not have: a party is never stepped after it finishes, and outputs are
pure. -/
