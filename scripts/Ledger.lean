/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Jin Xing Lim
-/

import Libsignal
import Protocols
import ProtocolsTest

/-! # Ledger probe

Prints the axiom closures recorded in `Protocols/LEDGER.md`. Run from the repository root after
`lake build` with `lake env lean scripts/Ledger.lean`. Not part of any Lake library. -/

#print axioms Protocols.Models.PQXDH.uakeInitiator_perfectlyCorrect
#print axioms Protocols.Models.PQXDH.uakeRecipient_perfectlyCorrect
#print axioms Protocols.Models.PQXDH.uakeInitiator_wellFormed
#print axioms Protocols.Models.PQXDH.uakeRecipient_wellFormed
#print axioms Protocols.Models.PQXDH.uakeInitiator_secure_dh
#print axioms Protocols.Models.PQXDH.uakeInitiator_secure_pq
#print axioms libsignal_protocol.pqxdh.pqxdh_initiate
#print axioms libsignal_protocol.pqxdh.pqxdh_accept

-- Realization closures: the KDF mirror in `Protocols/PQXDH/`.
#print axioms Protocols.PQXDH.deriveKeysTotal
#print axioms Protocols.PQXDH.deriveHK
#print axioms Protocols.PQXDH.deriveKeys
#print axioms Protocols.PQXDH.DeriveKeysTotal
#print axioms Protocols.PQXDH.kdfInput
#print axioms Protocols.PQXDH.pubSlice
#print axioms Protocols.PQXDH.sliceOfKey
#print axioms Protocols.PQXDH.pubBytes
#print axioms Protocols.PQXDH.ECPub
#print axioms Protocols.PQXDH.Key
#print axioms Protocols.PQXDH.HandshakeKeys
#print axioms Protocols.PQXDH.rootKeyBytes
#print axioms Protocols.PQXDH.chainKeyBytes
#print axioms Protocols.PQXDH.pqrKeyBytes
#print axioms Protocols.PQXDH.Bytes

-- Full realization: correctness and security statements, and the fault fixtures.
#print axioms Protocols.PQXDH.uakeInitiator_secure_dh
#print axioms Protocols.PQXDH.uakeInitiator_secure_dh_total
#print axioms Protocols.PQXDH.uakeInitiator_secure_pq
#print axioms Protocols.PQXDH.uakeInitiator_secure_pq_total
#print axioms Protocols.PQXDH.fullExp_noLostMass
#print axioms Protocols.PQXDH.wrapperAgreement_uakeInitiator
#print axioms Protocols.PQXDH.wrapperAgreement_uakeRecipient
#print axioms Protocols.PQXDH.coreCompletion_extracted
#print axioms Protocols.PQXDH.jointKeyAgreement_extracted
#print axioms Protocols.PQXDH.initiate_kdfInput_witness
#print axioms Protocols.PQXDH.accept_kdfInput_witness
#print axioms Protocols.PQXDH.alwaysPanic_fails
#print axioms Protocols.PQXDH.alwaysError_fails
#print axioms Protocols.PQXDH.alwaysDiverge_fails
