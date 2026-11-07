/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Jin Xing Lim
-/

import Protocols.Models.PQXDH
import Protocols.PQXDH.Correctness
import Protocols.PQXDH.Kdf
import Protocols.PQXDH.Security
import Protocols.Realization.RustOracleComp
import Protocols.Specs.Models.PQXDH
import Protocols.Specs.PQXDH
import Protocols.ToMathlib
import Protocols.ToVCVio

/-! # Protocol security

Umbrella for the protocol-security library: the models library, the realisation of each protocol
on the extracted code, the semantics shared by realisations, the spec summaries that freeze the
headline statements, and material staged for VCVio and Mathlib. `Protocols/README.md` describes
the layout and its dependency rule. -/
