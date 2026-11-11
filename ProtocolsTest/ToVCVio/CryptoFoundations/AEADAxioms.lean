/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.ToVCVio.CryptoFoundations.AEAD

/-!
# Axiom checks: the AEAD integrity lemmas

This file freezes the axiom closures of twelve lemmas about the integrity games in
`Protocols/ToVCVio/CryptoFoundations/AEAD.lean`. They are the four integrity lemmas, the two
advantage equalities and the six query-bound lemmas of the reductions. Each has a `#guard_msgs`
check on `#print axioms`, and the build fails when a closure changes. The file does not restate the
statements. No PQXDH theorem uses these lemmas.
-/

/-! ## Integrity lemmas -/

/--
info: 'AEAD.INT_CTXT_Advantage_le_INT_CTXT_VF_Advantage' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.INT_CTXT_Advantage_le_INT_CTXT_VF_Advantage

/--
info: 'AEAD.INT_CTXT_VF_Advantage_le_mul_INT_CTXT_Advantage' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.INT_CTXT_VF_Advantage_le_mul_INT_CTXT_Advantage

/--
info: 'AEAD.INT_CTXT_Advantage_le_INT_CTXT_D_Advantage' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.INT_CTXT_Advantage_le_INT_CTXT_D_Advantage

/--
info: 'AEAD.INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage

/-! ## Advantage equalities of the reductions -/

/--
info: 'AEAD.INT_CTXT_VF_Advantage_ctxtToVf' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.INT_CTXT_VF_Advantage_ctxtToVf

/--
info: 'AEAD.INT_CTXT_D_Advantage_ctxtToDec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.INT_CTXT_D_Advantage_ctxtToDec

/-! ## Query bounds of the reductions -/

/--
info: 'AEAD.ctxtToVf_encBound' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.ctxtToVf_encBound

/--
info: 'AEAD.ctxtToVf_vfBound' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.ctxtToVf_vfBound

/--
info: 'AEAD.ctxtToDec_encBound' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.ctxtToDec_encBound

/--
info: 'AEAD.ctxtToDec_decBound' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.ctxtToDec_decBound

/--
info: 'AEAD.vfToCtxt_encBound' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.vfToCtxt_encBound

/--
info: 'AEAD.decToCtxt_encBound' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AEAD.decToCtxt_encBound
