/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0, as in the PQXDH-model repository.
Authors: Ben Hamlin
-/
import VCVio.OracleComp.QueryTracking.Structures

universe u v

open OracleSpec OracleComp

namespace OracleSpec.QueryLog

variable {ι : Type u} {spec : OracleSpec ι}

/-- Check if an element `t` was ever queried and had the result `u`, given
  a log of queries. Relies on decidable equality of the domain and range
  types. -/
def wasQueriedWith [spec.DecidableEq] (log : QueryLog spec)
    (t : spec.Domain) (u : spec.Range t) : Bool :=
  decide (⟨t, u⟩ ∈ log)

/-- If `wasQueriedWith log t u` is true, then `wasQueried log t` is true. -/
lemma wasQueried_of_wasQueriedWith [spec.DecidableEq] {log : QueryLog spec}
    {t : spec.Domain} {u : spec.Range t} (h : log.wasQueriedWith t u = true) :
    log.wasQueried t = true := by
  have hmem : (⟨t, u⟩ : (t : spec.Domain) × spec.Range t) ∈ log := of_decide_eq_true h
  exact decide_eq_true ((getQ_ne_nil_iff_mem_map_fst log t).mpr
    (List.mem_map_of_mem hmem))

end OracleSpec.QueryLog
