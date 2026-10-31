/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Jin Xing Lim
-/

import Protocols.PQXDH.Model
import Protocols.PQXDH.Realization.Correctness
import Protocols.PQXDH.Realization.Kdf
import Protocols.PQXDH.Realization.Security
import Protocols.Realization.RustOracleComp
import Protocols.Specs.PQXDH.Realization
import Protocols.ToMathlib
import Protocols.ToVCVio

/-! # Protocol security

Umbrella for the protocol-security library: paper-level models, their realisation on the
extracted code, the semantics shared by realisations, the spec summaries that freeze the headline
statements, and material staged for VCVio and Mathlib. Layout follows SPQR-verify PR #503. -/
