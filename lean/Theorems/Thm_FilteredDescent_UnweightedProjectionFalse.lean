import Definitions.Def_FilteredDescent_Packet
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

/-!
# M9 — Unweighted projection is false (paper (54))

The naive "unweighted projection" claim — that conditioning on an event
preserves each slot's marginal — is false.  Concrete counterexample: two
tubes of unit weight, one packet slot, and the singleton event
`{U = (0,)}`.  The conditioned slot-0 marginal is `1`, while the
unconditioned marginal is `w 0 / W = 1 / 2`.  R5's `α⁻¹` factor
(here `α = 1 / 2`) is exactly what repairs the estimate.
-/

namespace FilteredDescent

theorem unweighted_projection_false :
    let w : Fin 2 → ℝ := fun _ => 1;
    let A : Finset (Fin 1 → Fin 2) := {fun _ => 0};
    (∑ U ∈ A, (if U 0 = 0 then packetLaw w U else 0)) / retainedMass w A ≠
      w 0 / ∑ i, w i := by
  simp only [packetLaw, retainedMass, Finset.sum_singleton]
  norm_num

end FilteredDescent
