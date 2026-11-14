/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Alessandro D'Angelo
-/
import Protocols.PQXDH.Kdf

/-!
# Helpers for the branch equations of the extracted entry points

The extracted code of `pqxdh_initiate` and `pqxdh_accept` is a chain of binds (`Std.bind`), with
the `?` operator written as `Result::branch` followed by a match. This file collects what the
proofs of the branch equations and of the witnesses need:

* `bind_eq_ok_iff` inverts a bind that returns a value;
* `kdfPrefixBytes`, `kdf_start` and `extend_prefix` describe the key-derivation input after some
  of its appends, and say when the next append cannot overflow;
* `kdfInput_inv` unfolds a successful `kdfInput` into the chain of appends that the two entry
  points inline.

None of these lemmas assumes the length of an output of a primitive. A bound on the assembled
bytes appears only where `extend_from_slice` can overflow.
-/

open Aeneas Aeneas.Std Result
open libsignal_protocol

namespace Protocols.PQXDH

universe u

/-- A bind returns a value exactly when its first operand returns a value and the continuation
returns the same value on it. -/
theorem bind_eq_ok_iff {α β : Type u} (x : Result α) (f : α → Result β) (b : β) :
    Std.bind x f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  constructor
  · intro h
    cases x with
    | ret a => exact ⟨a, rfl, by simpa using h⟩
    | vis i k =>
      change Std.bind (Result.vis i k) f = .ok b at h
      rw [bind_vis] at h
      exact absurd h.symm ok_not_vis
    | div => simp at h
  · rintro ⟨a, rfl, h⟩
    simpa using h

/-- A computation that satisfies a postcondition returns a value that satisfies it. -/
theorem exists_ok_of_spec {α : Type} {m : Result α} {p : α → Prop} (h : WP.spec m p) :
    ∃ v, m = .ok v ∧ p v :=
  deriveKeysTotal_spec_ok h

/-- Returning the error residual of `?` never returns a value. -/
theorem from_residual_Err_ne_Ok {T E F : Type} (inst : core.convert.From F E) (e : E) (x : T) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T inst
      (core.result.Result.Err e) ≠ ok (core.result.Result.Ok x) := by
  intro h
  simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    bind_tc_eq, bind_eq_ok_iff] at h
  obtain ⟨v, _, h⟩ := h
  simp at h

/-- The bytes of the key-derivation input after the 32 discontinuity bytes and the given slices,
in order. `kdfInputSliceBytes` is this list for the three agreements, the optional fourth and the
KEM secret. -/
def kdfPrefixBytes (parts : List (Slice U8)) : List U8 :=
  List.replicate 32 255#u8 ++ (parts.map (·.val)).flatten

theorem kdfPrefixBytes_append_single (parts : List (Slice U8)) (d : Slice U8) :
    kdfPrefixBytes (parts ++ [d]) = kdfPrefixBytes parts ++ d.val := by
  simp [kdfPrefixBytes]

theorem kdfPrefixBytes_length_le_append (parts : List (Slice U8)) (d : Slice U8) :
    (kdfPrefixBytes parts).length ≤ (kdfPrefixBytes (parts ++ [d])).length := by
  rw [kdfPrefixBytes_append_single, List.length_append]
  omega

/-- The 32 discontinuity bytes are appended to an empty vector: the start of every chain. -/
theorem kdf_start :
    ∃ (i : Usize) (s : Slice U8) (sec : alloc.vec.Vec U8),
      32#usize * 6#usize = ok i ∧
      lift (Array.repeat 32#usize 255#u8).to_slice = ok s ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 i) s =
        ok sec ∧
      sec.val = kdfPrefixBytes [] := by
  obtain ⟨i, hi, hival⟩ := exists_ok_of_spec (m := 32#usize * 6#usize)
    (p := fun i => i.val = 192) (by step*)
  have h_clone : ∀ x ∈ (Array.repeat 32#usize 255#u8).to_slice.val,
      core.clone.CloneU8.clone x = ok x := fun _ _ => rfl
  have hcap : ∀ j, (alloc.vec.Vec.with_capacity U8 j).val = [] := fun _ => rfl
  obtain ⟨sec, hsec, hsecval, -⟩ := exists_ok_of_spec
    (alloc.vec.Vec.extend_from_slice_spec core.clone.CloneU8
      (alloc.vec.Vec.with_capacity U8 i) (Array.repeat 32#usize 255#u8).to_slice h_clone
      (by
        simp only [alloc.vec.Vec.length, hcap, Slice.length, Array.val_to_slice, Array.repeat_val,
          UScalar.ofNatCore_val_eq, List.reduceReplicate, List.length_cons, List.length_nil,
          zero_add, Nat.reduceAdd]
        scalar_tac))
  refine ⟨i, _, sec, hi, rfl, hsec, ?_⟩
  simp [hsecval, hcap, Array.to_slice, kdfPrefixBytes]

/-- One more append to the key-derivation input succeeds when the result fits in a vector of
`Usize` length, and the vector then holds the bytes of the longer prefix. -/
theorem extend_prefix {sec : alloc.vec.Vec U8} {parts : List (Slice U8)} (d : Slice U8)
    (hsec : sec.val = kdfPrefixBytes parts)
    (hl : (kdfPrefixBytes (parts ++ [d])).length ≤ Usize.max) :
    ∃ sec' : alloc.vec.Vec U8,
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec d = ok sec' ∧
      sec'.val = kdfPrefixBytes (parts ++ [d]) := by
  have h_clone : ∀ x ∈ d.val, core.clone.CloneU8.clone x = ok x := fun _ _ => rfl
  rw [kdfPrefixBytes_append_single, List.length_append, ← hsec] at hl
  have hlen : sec.length + d.length ≤ Usize.max := by
    simpa [alloc.vec.Vec.length, Slice.length] using hl
  obtain ⟨sec', h, hval, -⟩ := exists_ok_of_spec
    (alloc.vec.Vec.extend_from_slice_spec core.clone.CloneU8 sec d h_clone hlen)
  exact ⟨sec', h, by rw [kdfPrefixBytes_append_single, ← hsec]; exact hval⟩

/-- If `extend_from_slice` returns a value, the longer prefix fits in a vector and the returned
vector holds the bytes of that prefix. -/
theorem extend_prefix_of_ok {sec sec' : alloc.vec.Vec U8} {parts : List (Slice U8)}
    {d : Slice U8} (hsec : sec.val = kdfPrefixBytes parts)
    (h : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec d = ok sec') :
    (kdfPrefixBytes (parts ++ [d])).length ≤ Usize.max ∧
      sec'.val = kdfPrefixBytes (parts ++ [d]) := by
  have hfits : (kdfPrefixBytes (parts ++ [d])).length ≤ Usize.max := by
    by_contra hnot
    have hlt : Usize.max < sec.length + d.length := by
      rw [kdfPrefixBytes_append_single, List.length_append, ← hsec] at hnot
      simpa [alloc.vec.Vec.length, Slice.length] using hnot
    rw [alloc.vec.Vec.extend_from_slice_overflow core.clone.CloneU8 sec d hlt] at h
    exact absurd h (by simp)
  obtain ⟨sec'', h'', hval⟩ := extend_prefix d hsec hfits
  rw [h''] at h
  simp only [Result.ok.injEq] at h
  subst h
  exact ⟨hfits, hval⟩

/-- The start of a chain, as an inversion: the vector after the 32 discontinuity bytes holds
those bytes. -/
theorem kdf_start_of_ok {i : Usize} {s : Slice U8} {sec : alloc.vec.Vec U8}
    (hi : 32#usize * 6#usize = ok i)
    (hs : lift (Array.repeat 32#usize 255#u8).to_slice = ok s)
    (hsec : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 i)
      s = ok sec) :
    sec.val = kdfPrefixBytes [] := by
  obtain ⟨i0, s0, sec0, hi0, hs0, hsec0, hval0⟩ := kdf_start
  rw [hi0] at hi
  rw [hs0] at hs
  simp only [Result.ok.injEq] at hi hs
  subst hi hs
  rw [hsec0] at hsec
  simp only [Result.ok.injEq] at hsec
  subst hsec
  exact hval0

/-- The appends of the first two agreements succeed when the bytes fit in a vector. -/
theorem extend_prefix_two {sec : alloc.vec.Vec U8} (d1 d2 : Slice U8)
    (hsec : sec.val = kdfPrefixBytes [])
    (hl : (kdfPrefixBytes [d1, d2]).length ≤ Usize.max) :
    ∃ sec2 sec3 : alloc.vec.Vec U8,
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec d1 = ok sec2 ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec2 d2 = ok sec3 ∧
      sec3.val = kdfPrefixBytes [d1, d2] := by
  obtain ⟨sec2, h2, hv2⟩ :=
    extend_prefix d1 hsec (le_trans (kdfPrefixBytes_length_le_append [d1] d2) hl)
  obtain ⟨sec3, h3, hv3⟩ := extend_prefix d2 hv2 hl
  exact ⟨sec2, sec3, h2, h3, hv3⟩

/-- The appends of the first three agreements succeed when the bytes fit in a vector. -/
theorem extend_prefix_three {sec : alloc.vec.Vec U8} (d1 d2 d3 : Slice U8)
    (hsec : sec.val = kdfPrefixBytes [])
    (hl : (kdfPrefixBytes [d1, d2, d3]).length ≤ Usize.max) :
    ∃ sec2 sec3 sec4 : alloc.vec.Vec U8,
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec d1 = ok sec2 ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec2 d2 = ok sec3 ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec3 d3 = ok sec4 ∧
      sec4.val = kdfPrefixBytes [d1, d2, d3] := by
  obtain ⟨sec2, sec3, h2, h3, hv3⟩ :=
    extend_prefix_two d1 d2 hsec (le_trans (kdfPrefixBytes_length_le_append [d1, d2] d3) hl)
  obtain ⟨sec4, h4, hv4⟩ := extend_prefix d3 hv3 hl
  exact ⟨sec2, sec3, sec4, h2, h3, h4, hv4⟩

/-- A successful `kdfInput` is the chain of appends that the two entry points inline: the 32
bytes of `0xFF`, the three agreements, the fourth when there is one, and the KEM secret. -/
theorem kdfInput_inv {d1 d2 d3 ss km : Slice U8} {d4 : Option (Slice U8)}
    (h : kdfInput d1 d2 d3 d4 ss = ok km) :
    ∃ (i : Usize) (s : Slice U8) (sec1 sec2 sec3 sec4 sec5 sec6 : alloc.vec.Vec U8),
      32#usize * 6#usize = ok i ∧
      lift (Array.repeat 32#usize 255#u8).to_slice = ok s ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 i) s =
        ok sec1 ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec1 d1 = ok sec2 ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec2 d2 = ok sec3 ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec3 d3 = ok sec4 ∧
      (match d4 with
        | none => sec5 = sec4
        | some d => alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec4 d = ok sec5) ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec5 ss = ok sec6 ∧
      km = alloc.vec.Vec.deref sec6 := by
  rcases d4 with _ | d <;>
    simp only [kdfInput, pure_tc_eq, bind_eq_ok_iff, Result.ok.injEq] at h <;>
    obtain ⟨i, hi, s, hs, sec1, h1, sec2, h2, sec3, h3, sec4, h4, h⟩ := h
  · obtain ⟨_, rfl, sec6, h6, hkm⟩ := h
    exact ⟨i, s, sec1, sec2, sec3, sec4, sec4, sec6, hi, hs, h1, h2, h3, h4, rfl, h6, hkm.symm⟩
  · obtain ⟨sec5, h5, sec6, h6, hkm⟩ := h
    exact ⟨i, s, sec1, sec2, sec3, sec4, sec5, sec6, hi, hs, h1, h2, h3, h4, h5, h6, hkm.symm⟩

end Protocols.PQXDH
