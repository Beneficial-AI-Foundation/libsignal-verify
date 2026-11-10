/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Mathlib.Tactic.Recall
import Libsignal.Proofs.Core.Address.ServiceIdBinary

/-!
# Spec summary: `rust/core/src/address.rs`

This file freezes the specifications of the items of `rust/core/src/address.rs`. Each theorem is
restated with `recall` and has a `#guard_msgs` check on the axioms it depends on.
-/

/-! ## `impl From<ServiceIdKind> for u8` -/

open Aeneas Aeneas.Std Result libsignal_core in
recall libsignal_core.U8.Insts.CoreConvertFromServiceIdKind.from_spec
    (value : address.ServiceIdKind) :
    U8.Insts.CoreConvertFromServiceIdKind.«from» value ⦃ result =>
      (value = .Aci → result = 0#u8) ∧
      (value = .Pni → result = 1#u8) ⦄

/--
info: 'libsignal_core.U8.Insts.CoreConvertFromServiceIdKind.from_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_core.U8.Insts.CoreConvertFromServiceIdKind.from_spec

/-! ## `ServiceId::kind` -/

open Aeneas Aeneas.Std Result libsignal_core.address in
recall libsignal_core.address.ServiceId.kind_spec (self : ServiceId) :
    ServiceId.kind self ⦃ (result : ServiceIdKind) =>
      (∀ aci, self = .Aci aci → result = .Aci) ∧
      (∀ pni, self = .Pni pni → result = .Pni) ⦄

/--
info: 'libsignal_core.address.ServiceId.kind_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_core.address.ServiceId.kind_spec

/-! ## `ServiceId::raw_uuid` -/

open Aeneas Aeneas.Std Result libsignal_core.address in
recall libsignal_core.address.ServiceId.raw_uuid_spec (self : ServiceId) :
    ServiceId.raw_uuid self ⦃ (result : uuid.Uuid) =>
      (∀ aci, self = .Aci aci → result = aci.uuid) ∧
      (∀ pni, self = .Pni pni → result = pni.uuid) ⦄

/--
info: 'libsignal_core.address.ServiceId.raw_uuid_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_core.address.ServiceId.raw_uuid_spec

/-! ## `ServiceId::service_id_fixed_width_binary` -/

open Aeneas Aeneas.Std Result libsignal_core.address in
recall libsignal_core.address.ServiceId.service_id_fixed_width_binary_spec (self : ServiceId) :
    ServiceId.service_id_fixed_width_binary self ⦃ result =>
      (∀ aci, self = .Aci aci → Array.index_usize result 0#usize = ok 0#u8) ∧
      (∀ pni, self = .Pni pni → Array.index_usize result 0#usize = ok 1#u8) ⦄

/--
info: 'libsignal_core.address.ServiceId.service_id_fixed_width_binary_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_core.address.ServiceId.service_id_fixed_width_binary_spec

/-! ## `ServiceId::service_id_binary` -/

open Aeneas Aeneas.Std Result libsignal_core.address in
recall libsignal_core.address.ServiceId.service_id_binary_spec (self : ServiceId) :
    ServiceId.service_id_binary self ⦃ result =>
      (∀ aci, self = .Aci aci → result.val = aci.uuid.bytes.val) ∧
      (∀ pni, self = .Pni pni → alloc.vec.Vec.index_usize result 0#usize = ok 1#u8) ⦄

/--
info: 'libsignal_core.address.ServiceId.service_id_binary_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_core.address.ServiceId.service_id_binary_spec
