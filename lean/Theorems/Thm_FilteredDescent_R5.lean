import Definitions.Def_FilteredDescent_Packet
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

/-!
# M1 — R5: retained-mass marginal domination (paper (9), (25))

R5 says: after conditioning the packet law on an event of retained mass
`α`, each slot's marginal is dominated by `α⁻¹` times the base tube law.
Before conditioning the domination constant is `1` (paper (18)).
-/

namespace FilteredDescent

/-- Constrained pi-sum: fixing one slot to `t`, the sum of product weights
factors as `w t * W^(r-1)`. -/
theorem constrained_pi_sum {n r : ℕ} (j : Fin r) (t : Fin n) (w : Fin n → ℝ) :
    ∑ U : Fin r → Fin n, (if U j = t then ∏ j', w (U j') else 0)
      = w t * (∑ i, w i) ^ (r - 1) := by
  set g : Fin r → Fin n → ℝ := fun j' i => if j' = j then (if i = t then w i else 0) else w i with hg
  have h1 : (∑ U : Fin r → Fin n, (if U j = t then ∏ j', w (U j') else 0))
      = ∑ U : Fin r → Fin n, ∏ j', g j' (U j') := by
    apply Finset.sum_congr rfl
    intro U _
    by_cases hUt : U j = t
    · simp only [hUt, if_true]
      apply Finset.prod_congr rfl
      intro j' _
      by_cases hjj : j' = j
      · simp [hg, hjj, hUt]
      · simp [hg, hjj]
    · simp only [hUt, if_false]
      have hz : g j (U j) = 0 := by simp [hg, hUt]
      exact (Finset.prod_eq_zero (Finset.mem_univ j) hz).symm
  have h2 : (∑ U : Fin r → Fin n, ∏ j', g j' (U j')) = ∏ j', ∑ i, g j' i := by
    have h := Finset.sum_prod_piFinset (Finset.univ : Finset (Fin n)) g
    simpa using h
  have h3 : (∏ j', ∑ i, g j' i) = w t * (∑ i, w i) ^ (r - 1) := by
    have hsum_j : ∑ i, g j i = w t := by
      simp [hg, Finset.sum_ite_eq']
    have hsum_other : ∀ j' : Fin r, j' ≠ j → ∑ i, g j' i = ∑ i, w i := by
      intro j' hj'
      apply Finset.sum_congr rfl
      intro i _
      simp [hg, hj']
    calc ∏ j', ∑ i, g j' i
        = (∑ i, g j i) * ∏ k ∈ Finset.univ.erase j, ∑ i, g k i := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      _ = w t * ∏ k ∈ Finset.univ.erase j, ∑ i, w i := by
          rw [hsum_j]
          congr 1
          apply Finset.prod_congr rfl
          intro k hk
          exact hsum_other k (Finset.ne_of_mem_erase hk)
      _ = w t * (∑ i, w i) ^ (r - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
          simp [Fintype.card_fin]
  rw [h1, h2, h3]

/-- Unconditioned slot marginal equals the base tube law (paper (18)). -/
theorem r5_marginal_bound_part1 {n r : ℕ} (j : Fin r) (t : Fin n) (w : Fin n → ℝ)
    (hr : 0 < r) (hW : 0 < ∑ i, w i) :
    slotMarginal w j t = w t / ∑ i, w i := by
  unfold slotMarginal packetLaw
  have hWne : (∑ i, w i) ≠ 0 := ne_of_gt hW
  have hWrm1_ne : (∑ i, w i) ^ (r - 1) ≠ 0 := pow_ne_zero _ hWne
  have hWr : (∑ i, w i) ^ r = (∑ i, w i) ^ (r - 1) * (∑ i, w i) := by
    have hr1 : r = (r - 1) + 1 := by omega
    conv_lhs => rw [hr1]
    rw [pow_succ]
  have hdiv : ∀ U : Fin r → Fin n,
      (if U j = t then (∏ j', w (U j')) / (∑ i, w i) ^ r else 0)
      = (if U j = t then ∏ j', w (U j') else 0) / (∑ i, w i) ^ r := by
    intro U
    by_cases hUt : U j = t <;> simp [hUt]
  calc ∑ U : Fin r → Fin n, (if U j = t then (∏ j', w (U j')) / (∑ i, w i) ^ r else 0)
      = (∑ U : Fin r → Fin n, (if U j = t then ∏ j', w (U j') else 0)) / (∑ i, w i) ^ r := by
        rw [Finset.sum_congr rfl (fun U _ => hdiv U)]
        simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = (w t * (∑ i, w i) ^ (r - 1)) / (∑ i, w i) ^ r := by
        rw [constrained_pi_sum j t w]
    _ = w t / ∑ i, w i := by
        rw [hWr, mul_comm ((∑ i, w i) ^ (r - 1)) (∑ i, w i)]
        exact mul_div_mul_right _ _ hWrm1_ne

theorem r5_marginal_bound {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i)
    (j : Fin r) (t : Fin n) :
    slotMarginal w j t = w t / ∑ i, w i ∧
    ∀ A : Finset (Fin r → Fin n), A.Nonempty →
    ∀ α : ℝ, α = retainedMass w A → 0 < α →
      (∑ U ∈ A, (if U j = t then packetLaw w U else 0)) / α
        ≤ (1 / α) * (w t / ∑ i, w i) := by
  refine ⟨r5_marginal_bound_part1 j t w hr hW, fun A hAne α hα hαpos => ?_⟩
  have hpl_nonneg : ∀ U : Fin r → Fin n, 0 ≤ packetLaw w U := by
    intro U
    unfold packetLaw
    apply div_nonneg
    · exact Finset.prod_nonneg (fun j' _ => hw (U j'))
    · exact pow_nonneg (le_of_lt hW) r
  have hle : (∑ U ∈ A, (if U j = t then packetLaw w U else 0))
      ≤ slotMarginal w j t := by
    unfold slotMarginal
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    intro U _ _
    by_cases hUt : U j = t
    · simp [hUt, hpl_nonneg U]
    · simp [hUt]
  rw [r5_marginal_bound_part1 j t w hr hW] at hle
  have h := div_le_div_of_nonneg_right hle (le_of_lt hαpos)
  calc (∑ U ∈ A, (if U j = t then packetLaw w U else 0)) / α
      ≤ (w t / ∑ i, w i) / α := h
    _ = (1 / α) * (w t / ∑ i, w i) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, one_div, mul_comm]

end FilteredDescent
