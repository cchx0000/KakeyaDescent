import Definitions.Def_FilteredDescent_Kernel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

/-!
# M3 — Insertion kernels: chain rule and confluence (paper (13)–(16))

The insertion kernel `K_{A,B}` is the conditional law of the `B`-slots
given the `A`-slots.  Paper (14) is the chain rule
`K_{A,C} = K_{B,C} · K_{A,B}` for `A ⊆ B ⊆ C`; paper (16) is the
confluence: inserting two slots in either order gives the same kernel.
(Paper (15), the pull-push/Fubini identity, is the measure-theoretic
transport used in the proofs.)
-/

namespace FilteredDescent

/-- Monotonicity of marginals: if `B ⊆ C` and `P ≥ 0`, then
`margLaw P C x ≤ margLaw P B x`, since agreement on `C` implies
agreement on `B`. -/
private lemma margLaw_mono {m n : ℕ} (P : (Fin m → Fin n) → ℝ) (hP : ∀ x, 0 ≤ P x)
    {B C : Finset (Fin m)} (hBC : B ⊆ C) (x : Fin m → Fin n) :
    margLaw P C x ≤ margLaw P B x := by
  unfold margLaw
  apply Finset.sum_le_sum
  intro y _
  by_cases hC : ∀ a ∈ C, y a = x a
  · have hB : ∀ a ∈ B, y a = x a := fun a ha => hC a (hBC ha)
    rw [if_pos hC, if_pos hB]
  · rw [if_neg hC]
    by_cases hB : ∀ a ∈ B, y a = x a
    · rw [if_pos hB]
      exact hP y
    · rw [if_neg hB]

/-- Marginals of a nonnegative law are nonnegative. -/
private lemma margLaw_nonneg {m n : ℕ} (P : (Fin m → Fin n) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (A : Finset (Fin m)) (x : Fin m → Fin n) : 0 ≤ margLaw P A x := by
  unfold margLaw
  apply Finset.sum_nonneg
  intro y _
  by_cases h : ∀ a ∈ A, y a = x a
  · rw [if_pos h]
    exact hP y
  · rw [if_neg h]

/-- A vanishing `B`-marginal forces the `C`-marginal to vanish when
`B ⊆ C` (for `P ≥ 0`). -/
private lemma margLaw_eq_zero_of_subset {m n : ℕ} (P : (Fin m → Fin n) → ℝ)
    (hP : ∀ x, 0 ≤ P x) {B C : Finset (Fin m)} (hBC : B ⊆ C) {x : Fin m → Fin n}
    (h : margLaw P B x = 0) : margLaw P C x = 0 :=
  le_antisymm (h ▸ margLaw_mono P hP hBC x) (margLaw_nonneg P hP C x)

/-- Chain rule for insertion kernels (paper (14)):
`K_{A,C} = K_{B,C} · K_{A,B}` for `A ⊆ B ⊆ C`. -/
private lemma chain_rule_aux {m n : ℕ} (P : (Fin m → Fin n) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (A B C : Finset (Fin m)) (_hAB : A ⊆ B) (hBC : B ⊆ C)
    (xC xA : Fin m → Fin n) :
    insKernel P A C xC xA
      = insKernel P B C xC xC * insKernel P A B xC xA := by
  unfold insKernel
  have hBtriv : ∀ a ∈ B, xC a = xC a := fun a _ => rfl
  by_cases hAgr : ∀ a ∈ A, xC a = xA a
  · by_cases hPA : margLaw P A xA ≠ 0
    · by_cases hPB : margLaw P B xC ≠ 0
      · -- All conditions hold: both sides are ratios of marginals.
        have hApos : (∀ a ∈ A, xC a = xA a) ∧ margLaw P A xA ≠ 0 := ⟨hAgr, hPA⟩
        have hBpos : (∀ a ∈ B, xC a = xC a) ∧ margLaw P B xC ≠ 0 := ⟨hBtriv, hPB⟩
        rw [if_pos hApos, if_pos hApos, if_pos hBpos, div_mul_div_cancel₀ hPB]
      · -- `margLaw P B xC = 0`: the first factor is 0, and the
        -- `C`-marginal vanishes too by monotonicity, so LHS = 0.
        have hPB0 : margLaw P B xC = 0 := not_ne_iff.mp hPB
        have hC0 : margLaw P C xC = 0 := margLaw_eq_zero_of_subset P hP hBC hPB0
        have hApos : (∀ a ∈ A, xC a = xA a) ∧ margLaw P A xA ≠ 0 := ⟨hAgr, hPA⟩
        have hBneg : ¬ ((∀ a ∈ B, xC a = xC a) ∧ margLaw P B xC ≠ 0) :=
          fun h => h.2 hPB0
        rw [if_pos hApos, if_pos hApos, if_neg hBneg, hC0, zero_div, zero_mul]
    · -- `margLaw P A xA = 0`: LHS and the second factor are 0.
      have hPA0 : margLaw P A xA = 0 := not_ne_iff.mp hPA
      have hAneg : ¬ ((∀ a ∈ A, xC a = xA a) ∧ margLaw P A xA ≠ 0) :=
        fun h => h.2 hPA0
      rw [if_neg hAneg, if_neg hAneg, mul_zero]
  · -- No agreement on `A`: LHS and the second factor are 0.
    have hAneg : ¬ ((∀ a ∈ A, xC a = xA a) ∧ margLaw P A xA ≠ 0) :=
      fun h => hAgr h.1
    rw [if_neg hAneg, if_neg hAneg, mul_zero]

theorem kernel_chain_confluence {m n : ℕ}
    (P : (Fin m → Fin n) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (A B C : Finset (Fin m)) (hAB : A ⊆ B) (hBC : B ⊆ C)
    (xC xA : Fin m → Fin n) :
    insKernel P A C xC xA
        = insKernel P B C xC xC * insKernel P A B xC xA ∧
    ∀ i j : Fin m, i ∉ A → j ∉ A → i ≠ j →
      insKernel P A (A ∪ {i, j}) xC xA
        = insKernel P (A ∪ {i}) (A ∪ {i, j}) xC xC
          * insKernel P A (A ∪ {i}) xC xA ∧
      insKernel P A (A ∪ {i, j}) xC xA
        = insKernel P (A ∪ {j}) (A ∪ {i, j}) xC xC
          * insKernel P A (A ∪ {j}) xC xA := by
  refine ⟨chain_rule_aux P hP A B C hAB hBC xC xA, fun i j _ _ _ => ⟨?_, ?_⟩⟩
  · -- Insert `i` first: chain rule with `B := A ∪ {i}`.
    exact chain_rule_aux P hP _ _ _
      Finset.subset_union_left
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i {j})))
      _ _
  · -- Insert `j` first: chain rule with `B := A ∪ {j}`.
    exact chain_rule_aux P hP _ _ _
      Finset.subset_union_left
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.singleton_subset_iff.mpr
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))))
      _ _

end FilteredDescent
