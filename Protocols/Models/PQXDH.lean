/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Jin Xing Lim
-/

import Protocols.Models.PQXDH.Basic
import Protocols.Models.PQXDH.UAKE.Correctness
import Protocols.Models.PQXDH.UAKE.CorrectnessLemmas
import Protocols.Models.PQXDH.UAKE.Defs
import Protocols.Models.PQXDH.UAKE.Security
import Protocols.Models.PQXDH.UAKE.SecurityLemmas
import Protocols.Models.PQXDH.UAKE.WellFormed
import Protocols.Models.PQXDH.UAKE.WellFormedLemmas

/-! # The PQXDH model

Paper-level model of PQXDH over abstract primitives, ported from PQXDH-model at f862593 with
the namespace `PQXDH` renamed `Protocols.Models.PQXDH`: the protocol procedures and their parameters
in `Basic`, the two UAKE schemes `uakeInitiator` and `uakeRecipient` in `UAKE.Defs`, their
perfect correctness in `UAKE.Correctness` and their well-formedness in `UAKE.WellFormed`, with
the supporting lemmas in `UAKE.CorrectnessLemmas` and `UAKE.WellFormedLemmas`, the game hops
in `UAKE.SecurityLemmas`, five of them admitted, and the two security theorems
`uakeInitiator_secure_dh` and `uakeInitiator_secure_pq` in `UAKE.Security`. -/
