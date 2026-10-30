/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.WellFormedLemmas

/-!
# Well-formedness of the PQXDH Model's UAKE Schemes

`UAKE.Scheme.WellFormed` for both orientations of the model scheme: each
party produces output exactly when its protocol run completes, each party's
output function is pure, and an honest run transfers exactly `rounds` messages.
The supporting lemmas live in `WellFormedLemmas.lean`.
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace Protocols.PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

/-- The T=Bob model scheme is well-formed: both parties output only at
  completion, both output functions are pure, and an honest run transfers
  exactly 3 messages.

  The hypothesis `hkem` (perfect KEM correctness) is an idealization. It is false for
  production Kyber, whose decapsulation can return a different shared secret with a small
  nonzero probability, so this statement does not apply to production Kyber. -/
theorem uakeInitiator_wellFormed
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    (uakeInitiator P msg hasOPK).WellFormed := by
  refine ⟨initiator_outputsOnlyAtCompletion P,
    recipient_outputsOnlyAtCompletion P hasOPK,
    initiator_pureOutput P, recipient_pureOutput P hasOPK, ?_⟩
  intro uk tk hsetup uOut tOut ms hrun
  exact runHonest_length_initiator P msg hasOPK hsig hkem haead hsetup hrun

/-- The T=Alice model scheme is well-formed: both parties output only at
  completion, both output functions are pure, and an honest run transfers
  exactly 2 messages.

  The hypothesis `hkem` (perfect KEM correctness) is an idealization. It is false for
  production Kyber, whose decapsulation can return a different shared secret with a small
  nonzero probability, so this statement does not apply to production Kyber. -/
theorem uakeRecipient_wellFormed
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    (uakeRecipient P msg hasOPK).WellFormed := by
  refine ⟨recipientNoConfirm_outputsOnlyAtCompletion P hasOPK,
    initiatorNoConfirm_outputsOnlyAtCompletion P,
    recipientNoConfirm_pureOutput P hasOPK, initiatorNoConfirm_pureOutput P, ?_⟩
  intro uk tk hsetup uOut tOut ms hrun
  replace hsetup : (uk, tk) ∈ support (Prod.swap <$> setup P msg) := hsetup
  simp only [support_map, Set.mem_image, Prod.exists, Prod.swap_prod_mk,
    Prod.mk.injEq] at hsetup
  obtain ⟨uk₀, tk₀, hsetup₀, htk, huk⟩ := hsetup
  subst huk htk
  exact runHonest_length_recipient P msg hasOPK hsig hkem haead hsetup₀ hrun

end Protocols.PQXDH
