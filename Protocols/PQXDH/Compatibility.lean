/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Beneficial AI Foundation
-/

import Libsignal
import VCVio.OracleComp.ProbCompLift
import PQXDH.Spec.UAKE.Security
import PQXDH.Spec.UAKE.Correctness
import PQXDH.Spec.UAKE.WellFormed
import PQXDH.AKE.UAKE.Transport

/-! The extracted operations and abstract PQXDH endpoints share one Lean environment.
These checks assert availability, not a correspondence theorem. Imported security
results retain their upstream proof admissions. -/

#check libsignal_protocol.pqxdh.pqxdh_initiate
#check libsignal_protocol.pqxdh.pqxdh_accept
#check PQXDH.uakeInitiator_secure_dh
#check PQXDH.uakeInitiator_secure_pq
#check PQXDH.uakeInitiator_perfectlyCorrect
#check PQXDH.uakeRecipient_perfectlyCorrect
#check PQXDH.uakeInitiator_wellFormed
#check PQXDH.uakeRecipient_wellFormed
#check AKE.UAKE.Exp_transport
