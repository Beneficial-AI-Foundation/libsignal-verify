/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Jin Xing Lim
-/

import Protocols.PQXDH.Model.Basic
import Protocols.PQXDH.Model.UAKE.Correctness
import Protocols.PQXDH.Model.UAKE.CorrectnessLemmas
import Protocols.PQXDH.Model.UAKE.Defs

/-! # The PQXDH model

Paper-level model of PQXDH over abstract primitives, ported from PQXDH-model at f862593 with
the namespace `PQXDH` renamed `Protocols.PQXDH`: the protocol procedures and their parameters
in `Basic`, the two UAKE schemes `uakeInitiator` and `uakeRecipient` in `UAKE.Defs`, and their
perfect correctness in `UAKE.Correctness`, with the supporting lemmas in `UAKE.CorrectnessLemmas`. -/
