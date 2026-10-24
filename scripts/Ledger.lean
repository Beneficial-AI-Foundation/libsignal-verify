/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Jin Xing Lim
-/

import Libsignal
import Protocols

/-! # Ledger probe

Prints the axiom closures recorded in `Protocols/LEDGER.md`. Run from the repository root after
`lake build` with `lake env lean scripts/Ledger.lean`. Not part of any Lake library. -/

#print axioms Protocols.PQXDH.uakeInitiator_perfectlyCorrect
#print axioms Protocols.PQXDH.uakeRecipient_perfectlyCorrect
#print axioms Protocols.PQXDH.uakeInitiator_wellFormed
#print axioms Protocols.PQXDH.uakeRecipient_wellFormed
#print axioms Protocols.PQXDH.uakeInitiator_secure_dh
#print axioms Protocols.PQXDH.uakeInitiator_secure_pq
#print axioms libsignal_protocol.pqxdh.pqxdh_initiate
#print axioms libsignal_protocol.pqxdh.pqxdh_accept
