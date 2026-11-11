/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Libsignal.Proofs.Std.Alloc.Vec.ExtendFromSlice
import Libsignal.Proofs.Protocol.Pqxdh.HandshakeKeys.Derive
import Protocols.PQXDH.Defs

/-!
# Lean mirror of the extracted PQXDH key derivation

A Lean-level mirror of the KDF step of the extracted `pqxdh_initiate` and `pqxdh_accept`:
`kdfInput` assembles the KDF input (32 bytes of `0xFF`, the DH outputs, the optional fourth DH
output and the KEM shared secret) and `deriveHK` passes it to the extracted
`pqxdh.HandshakeKeys.derive`. The mirror restates the input layout of the extracted functions; this
file does not prove that it agrees with them.

`kdfInput_spec` gives the exact bytes that `kdfInput` returns, `kdfInputSliceBytes`, for slices
of any length under one bound on the total length; `kdfInput_fixed_spec` adds the length, 160 or
192 bytes, for 32-byte components. `deriveKeysTotal` proves `DeriveKeysTotal`, the totality of
`deriveHK`, from the contract `HkdfSha256Contract` on the opaque `crypto.hkdf_sha256`, through
`HandshakeKeys.derive_spec`.

**Source**: `PQXDH/Aeneas/Full/UAKE/SecurityDefs.lean` of libsignal-docs-and-models, the
declarations of the same names. The source opens a `noncomputable section`; here only `deriveHK`
and `deriveKeys`, which call the extracted derivation, are marked `noncomputable`.
-/

open Aeneas Aeneas.Std Result
open libsignal_protocol

namespace Protocols.PQXDH

/-- The raw bytes of a curve25519 public key. -/
def pubBytes (p : ECPub) : Key :=
  match p.key with
  | .DjbPublicKey a => a

/-- View a 32-byte key as a slice. -/
def sliceOfKey (k : Key) : Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) :=
  Aeneas.Std.lift (Aeneas.Std.Array.to_slice k)

/-- View a public key's bytes as a slice. -/
def pubSlice (p : ECPub) : Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) :=
  sliceOfKey (pubBytes p)

/-- Mirror of the extracted KDF input layout: 32 bytes of 0xFF followed by the
  DH outputs and the KEM secret. -/
def kdfInput (dh1 dh2 dh3 : Aeneas.Std.Slice Aeneas.Std.U8)
    (dh4 : Option (Aeneas.Std.Slice Aeneas.Std.U8))
    (ss : Aeneas.Std.Slice Aeneas.Std.U8) :
    Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) := do
  let i ← 32#usize * 6#usize
  let secrets := Aeneas.Std.alloc.vec.Vec.with_capacity Aeneas.Std.U8 i
  let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice
    (Aeneas.Std.Array.repeat 32#usize 255#u8))
  let secrets1 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets s
  let secrets2 ←
    Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets1 dh1
  let secrets3 ←
    Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets2 dh2
  let secrets4 ←
    Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets3 dh3
  let secrets5 ← match dh4 with
    | none => pure secrets4
    | some d => Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets4 d
  let secrets6 ←
    Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets5 ss
  pure (Aeneas.Std.alloc.vec.Vec.deref secrets6)

/-- The bytes that `kdfInput` assembles: 32 bytes of `0xFF`, then `dh1`, `dh2` and `dh3`, then
`dh4` when there is one, then the KEM secret `ss`. This is the slice form of `kdfInputBytes` in
`SecurityDefs.lean`, which takes 32-byte keys. -/
def kdfInputSliceBytes (dh1 dh2 dh3 : Slice U8) (dh4 : Option (Slice U8)) (ss : Slice U8) :
    List U8 :=
  let dh4Bytes := match dh4 with
    | none => []
    | some d => d.val
  List.replicate 32 255#u8 ++ dh1.val ++ dh2.val ++ dh3.val ++ dh4Bytes ++ ss.val

/-- For slices of any length, if the assembled byte list has length at most `Usize.max`,
`kdfInput` succeeds and returns `kdfInputSliceBytes`. -/
@[step]
theorem kdfInput_spec (dh1 dh2 dh3 : Slice U8) (dh4 : Option (Slice U8)) (ss : Slice U8)
    (h_len : (kdfInputSliceBytes dh1 dh2 dh3 dh4 ss).length ≤ Usize.max) :
    kdfInput dh1 dh2 dh3 dh4 ss ⦃ inp =>
      inp.val = kdfInputSliceBytes dh1 dh2 dh3 dh4 ss ⦄ := by
  open Aeneas.Std.alloc.vec in
  have h_cap : ∀ j, (Vec.with_capacity U8 j).length = 0 := fun _ => rfl
  open Aeneas.Std.alloc.vec in
  have h_nil : ∀ j, (Vec.with_capacity U8 j).val = [] := fun _ => rfl
  open Aeneas.Std.alloc.vec in
  rcases dh4 with _ | d <;>
    simp only [kdfInputSliceBytes, List.length_append, List.length_replicate,
      List.append_nil] at h_len <;>
    unfold kdfInput <;> step* <;>
    simp [kdfInputSliceBytes, Vec.deref, Slice.from_val, *]

/-- For DH outputs and a KEM secret given as 32-byte arrays, `kdfInput` succeeds and returns
`kdfInputSliceBytes`, of length 160 without the fourth DH output and 192 with it. -/
theorem kdfInput_fixed_spec (dh1 dh2 dh3 : Array U8 32#usize) (dh4 : Option (Array U8 32#usize))
    (ss : Array U8 32#usize) :
    kdfInput dh1.to_slice dh2.to_slice dh3.to_slice (dh4.map (·.to_slice)) ss.to_slice
      ⦃ inp =>
        inp.val = kdfInputSliceBytes dh1.to_slice dh2.to_slice dh3.to_slice
          (dh4.map (·.to_slice)) ss.to_slice ∧
        inp.length = if dh4.isSome then 192 else 160 ⦄ := by
  have h192 : 192 ≤ Usize.max := by
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max, U64.max] <;> scalar_tac
  have h_len : (kdfInputSliceBytes dh1.to_slice dh2.to_slice dh3.to_slice
      (dh4.map (·.to_slice)) ss.to_slice).length = if dh4.isSome then 192 else 160 := by
    rcases dh4 with _ | d <;> simp [kdfInputSliceBytes]
  refine WP.spec_mono (kdfInput_spec _ _ _ _ _ ?_) ?_
  · rw [h_len]; split <;> omega
  · intro inp h_val
    exact ⟨h_val, by simp [Slice.length, h_val, h_len]⟩

/-- Run the extracted HKDF derivation on the assembled KDF input. -/
noncomputable def deriveHK (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key) :
    Aeneas.Std.Result pqxdh.HandshakeKeys := do
  let s1 ← pubSlice dh1
  let s2 ← pubSlice dh2
  let s3 ← pubSlice dh3
  let s4 ← match dh4 with
    | none => pure none
    | some d => do let x ← pubSlice d; pure (some x)
  let ssS ← sliceOfKey ss
  let inp ← kdfInput s1 s2 s3 s4 ssS
  pqxdh.HandshakeKeys.derive inp

/-- The extracted key derivation, split into `(root_key, chain_key,
  pqr_key)`. -/
noncomputable def deriveKeys (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key) :
    Aeneas.Std.Result (Key × Key × Key) := do
  let hk ← deriveHK dh1 dh2 dh3 dh4 ss
  pure (rootKeyBytes hk, chainKeyBytes hk, pqrKeyBytes hk)

/-- Totality of the extracted KDF: `deriveHK` succeeds on every input. -/
def DeriveKeysTotal : Prop :=
  ∀ (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key),
    ∃ hk, deriveHK dh1 dh2 dh3 dh4 ss = .ok hk

/-- **`deriveHK` is total under the HKDF contract**: for any MAC interface `H` and under
`HkdfSha256Contract H`, `deriveHK` succeeds on all public keys, with or without the fourth DH
output, and every 32-byte shared secret. The assembled input has at most 192 bytes, so no append
overflows, and `HandshakeKeys.derive_spec` gives success of the derivation. -/
theorem deriveKeysTotal
    (H : libsignal_protocol.crypto.HmacSha256)
    (h_hkdf : libsignal_protocol.crypto.HkdfSha256Contract H) :
    DeriveKeysTotal := by
  intro dh1 dh2 dh3 dh4 ss
  have h192 : 192 ≤ Usize.max := by
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max, U64.max] <;> scalar_tac
  obtain ⟨inp, h_inp⟩ : ∃ inp, kdfInput (pubBytes dh1).to_slice (pubBytes dh2).to_slice
      (pubBytes dh3).to_slice (dh4.map fun d => (pubBytes d).to_slice) ss.to_slice = ok inp := by
    have h : kdfInput (pubBytes dh1).to_slice (pubBytes dh2).to_slice (pubBytes dh3).to_slice
        (dh4.map fun d => (pubBytes d).to_slice) ss.to_slice ⦃ _ => True ⦄ := by
      have h_cap : ∀ j, (alloc.vec.Vec.with_capacity U8 j).length = 0 := fun _ => rfl
      unfold kdfInput
      rcases dh4 with _ | d <;> dsimp only [Option.map] <;> step*
    obtain ⟨inp, h_eq, -⟩ := WP.spec_imp_exists h
    exact ⟨inp, h_eq⟩
  obtain ⟨keys, h_keys, -⟩ := WP.spec_imp_exists (pqxdh.HandshakeKeys.derive_spec H h_hkdf inp)
  refine ⟨keys, ?_⟩
  rcases dh4 with _ | d <;> simp_all [deriveHK, pubSlice, sliceOfKey, lift, pure_tc_eq]

end Protocols.PQXDH
