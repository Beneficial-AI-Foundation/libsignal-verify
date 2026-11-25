/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Curve25519.X25519
import Curve25519.Montgomery

/-!
# Facts about X25519 and clamping

Four facts about the RFC 7748 function `X25519` of the fork's mathematics library and the
clamping of its scalars. They are stated with the definitions of the `Curve25519` library of the
curve25519-dalek fork (`Curve25519.X25519` and `Curve25519.Montgomery`), which is the only part of
the fork that this module imports. Each fact is proved from the fork's theorems, with no assumption
beyond Lean's axioms: `Protocols/Specs/PQXDH.lean` checks the axioms that each depends on.

* `x25519_basepoint_comm`: the two parties of a Diffie-Hellman exchange from the base point
  compute the same 32 bytes.
* `L_not_dvd_clamp`: a clamped scalar is not a multiple of the order of the base point.
* `x25519_basepoint_ne_zero`: the shared secret of the private key `a` and the public key
  `X25519 b 9` is not the all-zero encoding.
* `clamp_clamp`: clamping a scalar twice gives the same value as clamping it once.
-/

namespace Protocols.PQXDH

open curve25519

/-- For all 32-byte scalars `a` and `b`, `X25519` with `a` of the public key `X25519 b 9` equals
`X25519` with `b` of the public key `X25519 a 9`. Here `9` is the encoded u-coordinate of the
base point. -/
theorem x25519_basepoint_comm (a b : Vector UInt8 32) :
    X25519 a (X25519 b (encodeUCoordinate 9)) = X25519 b (X25519 a (encodeUCoordinate 9)) :=
  X25519_X25519_comm a b _

/-- A clamped scalar is not a multiple of the order `L` of the base point. -/
theorem L_not_dvd_clamp (k : ℕ) : ¬ L ∣ clamp k := by
  rintro ⟨t, ht⟩
  have hodd : Nat.Coprime 8 L := by
    rw [L_eq_numeral]
    norm_num
  have h8 : 8 ∣ L * t := by
    rw [← ht]
    exact Nat.dvd_of_mod_eq_zero (clamp_mod_eight k)
  have ht8 : 8 ∣ t := hodd.dvd_of_dvd_mul_left h8
  have hbig : 2 ^ 255 < L * 8 := by
    rw [L_eq_numeral]
    norm_num
  have h1 : L * t < 2 ^ 255 := by
    rw [← ht]
    exact clamp_lt k
  have h2 : 2 ^ 254 ≤ L * t := by
    rw [← ht]
    exact two_pow_254_le_clamp k
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0
    simp at h2
  · have hle : L * 8 ≤ L * t := Nat.mul_le_mul_left _ (Nat.le_of_dvd hpos ht8)
    exact absurd (hbig.trans_le hle) (not_lt.mpr h1.le)

/-- For all 32-byte scalars `a` and `b`, the shared secret `X25519 a (X25519 b 9)` of the private
key `a` and the public key `X25519 b 9` is not the all-zero encoding. -/
theorem x25519_basepoint_ne_zero (a b : Vector UInt8 32) :
    X25519 a (X25519 b (encodeUCoordinate 9)) ≠ encodeUCoordinate 0 := by
  rw [X25519_basepoint b,
    X25519_eq_u_nsmul a _ (decodeScalar25519 b • montgomeryBasepoint)
      (decodeUCoordinate_encodeUCoordinate _).symm]
  intro h
  have hu : (decodeScalar25519 a • decodeScalar25519 b • montgomeryBasepoint).u = 0 := by
    have := congrArg decodeUCoordinate h
    rwa [decodeUCoordinate_encodeUCoordinate, decodeUCoordinate_encodeUCoordinate] at this
  have h2 := MontgomeryModel.add_self_eq_zero_of_u_eq_zero hu
  rw [← two_nsmul, smul_smul, smul_smul] at h2
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h2
  rw [addOrderOf_montgomeryBasepoint] at hdvd
  have hp := L_prime
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have h2L : L ≤ 2 := Nat.le_of_dvd (by norm_num) h
      have : ¬ L ≤ 2 := by
        rw [L_eq_numeral]
        norm_num
      exact absurd h2L this
    · exact L_not_dvd_clamp _ h
  · exact L_not_dvd_clamp _ h

/-- RFC 7748 clamping is idempotent: `clamp (clamp k) = clamp k`. -/
theorem clamp_clamp (k : ℕ) : clamp (clamp k) = clamp k := by
  unfold clamp
  omega

end Protocols.PQXDH
