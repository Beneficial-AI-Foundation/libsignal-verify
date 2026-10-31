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

#print axioms Protocols.PQXDH.uakeInitiator_perfectlyCorrect
#print axioms Protocols.PQXDH.uakeRecipient_perfectlyCorrect
#print axioms Protocols.PQXDH.uakeInitiator_wellFormed
#print axioms Protocols.PQXDH.uakeRecipient_wellFormed
#print axioms Protocols.PQXDH.uakeInitiator_secure_dh
#print axioms Protocols.PQXDH.uakeInitiator_secure_pq
#print axioms libsignal_protocol.pqxdh.pqxdh_initiate
#print axioms libsignal_protocol.pqxdh.pqxdh_accept

-- Realization closures: the KDF mirror in `Protocols/PQXDH/Realization/`.
#print axioms Protocols.PQXDH.Realization.deriveKeysTotal
#print axioms Protocols.PQXDH.Realization.deriveHK
#print axioms Protocols.PQXDH.Realization.deriveKeys
#print axioms Protocols.PQXDH.Realization.DeriveKeysTotal
#print axioms Protocols.PQXDH.Realization.kdfInput
#print axioms Protocols.PQXDH.Realization.pubSlice
#print axioms Protocols.PQXDH.Realization.sliceOfKey
#print axioms Protocols.PQXDH.Realization.pubBytes
#print axioms Protocols.PQXDH.Realization.ECPub
#print axioms Protocols.PQXDH.Realization.Key
#print axioms Protocols.PQXDH.Realization.HandshakeKeys
#print axioms Protocols.PQXDH.Realization.rootKeyBytes
#print axioms Protocols.PQXDH.Realization.chainKeyBytes
#print axioms Protocols.PQXDH.Realization.pqrKeyBytes
#print axioms Protocols.PQXDH.Realization.Bytes

-- Full realization: correctness and security statements, and the fault fixtures.
#print axioms Protocols.PQXDH.Realization.uakeInitiator_secure_dh
#print axioms Protocols.PQXDH.Realization.uakeInitiator_secure_dh_total
#print axioms Protocols.PQXDH.Realization.uakeInitiator_secure_pq
#print axioms Protocols.PQXDH.Realization.uakeInitiator_secure_pq_total
#print axioms Protocols.PQXDH.Realization.fullExp_noLostMass
#print axioms Protocols.PQXDH.Realization.wrapperAgreement_uakeInitiator
#print axioms Protocols.PQXDH.Realization.wrapperAgreement_uakeRecipient
#print axioms Protocols.PQXDH.Realization.coreCompletion_extracted
#print axioms Protocols.PQXDH.Realization.jointKeyAgreement_extracted
#print axioms Protocols.PQXDH.Realization.initiate_kdfInput_witness
#print axioms Protocols.PQXDH.Realization.accept_kdfInput_witness
#print axioms Protocols.PQXDH.Realization.alwaysPanic_fails
#print axioms Protocols.PQXDH.Realization.alwaysError_fails
#print axioms Protocols.PQXDH.Realization.alwaysDiverge_fails
