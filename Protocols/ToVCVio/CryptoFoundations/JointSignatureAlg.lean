/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import VCVio.CryptoFoundations.SignatureAlg

/-!
# Joint unforgeability of a signature key that is also used for agreement

A signing key that also takes part in a second computation, such as the Diffie-Hellman agreement of
the same identity key, is used in two places. An adversary against the signature scheme must then
be allowed to see the second use. This file defines the game of existential unforgeability under
chosen messages with a second oracle on the secret key.

`SignatureAlg.jointUnforgeableExp` draws one key pair from `sigAlg.keygen` and runs the adversary
with three oracles: uniform sampling, signing, and the second use `agree sk`. Signing queries are
recorded. Queries to the second oracle are not recorded and carry no freshness condition. The
adversary wins when its signature verifies and its message was never submitted to the signing
oracle.

VCVio's `SignatureAlg.unforgeableExperiment` has the signing oracle only. Its strong variant is
not an option here either: it is false of XEdDSA, whose verification accepts `(R, s + ℓ)` whenever
it accepts `(R, s)`.

The definitions in this file are AI-written.
-/

open OracleSpec OracleComp
open scoped ENNReal

namespace SignatureAlg

variable {M PK SK S X Y : Type}

/-- The oracles of the joint game: uniform sampling, signing a message in `M` with a signature in
`S`, and the second use of the secret key on an input in `X` with an output in `Y`. -/
abbrev JointSpec (M S X Y : Type) :=
  unifSpec + ((M →ₒ S) + (X →ₒ Y))

/-- An adversary in the joint game for `sigAlg` and the second use `agree`: from the public key,
with the oracles of `JointSpec`, it outputs a message and a signature. The scheme and `agree`
index the adversary by their types and are not stored. -/
structure JointAdversary (_sigAlg : SignatureAlg ProbComp M PK SK S) (_agree : SK → X → Y) where
  /-- The adversary's computation. -/
  main : PK → OracleComp (JointSpec M S X Y) (M × S)

/-- The oracles of the joint game for the key pair `(pk, sk)`. Uniform queries are forwarded.
Signing records the message and runs `sigAlg.sign pk sk`. The second use answers `agree sk x`
without recording. -/
def jointImpl (sigAlg : SignatureAlg ProbComp M PK SK S) (agree : SK → X → Y)
    (pk : PK) (sk : SK) : QueryImpl (JointSpec M S X Y) (StateT (List M) ProbComp) :=
  let unifImpl : QueryImpl unifSpec (StateT (List M) ProbComp) := fun t =>
    liftM ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) t)
  let signImpl : QueryImpl (M →ₒ S) (StateT (List M) ProbComp) := fun m => do
    modify (m :: ·)
    liftM (sigAlg.sign pk sk m)
  let agreeImpl : QueryImpl (X →ₒ Y) (StateT (List M) ProbComp) := fun x =>
    pure (agree sk x)
  unifImpl + (signImpl + agreeImpl)

/-- The joint unforgeability game: draw one key pair, run the adversary with the oracles of
`jointImpl`, verify its output, and win when the signature verifies and the message was never
signed. -/
def jointUnforgeableExp [DecidableEq M] (sigAlg : SignatureAlg ProbComp M PK SK S)
    (agree : SK → X → Y) (A : JointAdversary sigAlg agree) : ProbComp Bool := do
  let (pk, sk) ← sigAlg.keygen
  let ((m, σ), signed) ← (simulateQ (jointImpl sigAlg agree pk sk) (A.main pk)).run []
  let ok ← sigAlg.verify pk m σ
  pure (ok && decide (m ∉ signed))

/-- The success probability of a joint adversary. -/
noncomputable def JointAdversary.advantage [DecidableEq M]
    {sigAlg : SignatureAlg ProbComp M PK SK S} {agree : SK → X → Y}
    (A : JointAdversary sigAlg agree) : ℝ≥0∞ :=
  Pr{let y ← (jointUnforgeableExp sigAlg agree A)}[y = true]

end SignatureAlg
