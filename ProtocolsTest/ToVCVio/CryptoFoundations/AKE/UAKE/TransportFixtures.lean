/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/

import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Transport

/-!
# Transport Fixtures

The transport theorems instantiated at the identity simulation `Party.Sim.refl`. Each
example applies the generic theorem to the identity maps and checks that its hypotheses
are discharged there, so the reflexive case is a direct instance of the transport rather
than a separate argument. Only a lawful monad is assumed, the setting of the transport
theorems themselves.
-/

open OracleSpec OracleComp

namespace AKE.UAKE

namespace TransportFixtures

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- `runHonest_transport` at the identity simulation of both parties. -/
example {W InP OutP InQ OutQ : Type} (P : Party m InP W OutP) (Q : Party m InQ W OutQ)
    (p : InP) (q : InQ) (fuel : ℕ) :
    Party.runHonest P Q (id p) (id q) fuel = Party.runHonest P Q p q fuel :=
  Party.runHonest_transport (Party.Sim.refl P) (Party.Sim.refl Q) p q fuel

/-- `Exp_transport` at the identity simulation of both parties. The setup hypothesis is
discharged by `Prod.map_id` and `id_map`. By `Adversary.transport_id` the transported
adversary on the right is `A` itself. -/
example {K UK TK W : Type} [SampleableType K] [DecidableEq W] (lift : ProbCompLift m)
    (proto : Scheme m K UK TK W) (A : Adversary proto) :
    Exp lift A = Exp lift (Adversary.transport (proto₁ := proto) (proto₂ := proto) id A) :=
  Exp_transport lift (Party.Sim.refl proto.U) (Party.Sim.refl proto.T) rfl
    (by rw [Prod.map_id, id_map]) A

end TransportFixtures

end AKE.UAKE
