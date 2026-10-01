import Definitions.Def_FilteredDescent_Tree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# M6a — Common-source duplicate closure (paper (143)–(155))

`X^{root}` splits exactly into the geometric and duplicate parts
(`X^{root} = X^{geom} + X^{dup}`).  The duplicate part — root-cross pairs
ending in the same terminal tube — is closed by the per-carrier aggregate
bound (the finite form of paper (150)–(151)):

  `X^{dup} ≤ (#carriers) · (A · B) · ∫N`.
-/

namespace FilteredDescent

theorem duplicate_closure {α : Type} [DecidableEq α] {n m : ℕ}
    (T : Finset (List α))
    (u : List α → ℝ) (hu : ∀ γ ∈ treeLeaves T, 0 ≤ u γ)
    (termTube : List α → Fin n) (carrier : List α → Fin m)
    (A B : ℝ)
    (hagg :
      ∀ t : Fin n, ∀ c : Fin m,
        ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t ∧ carrier γ = c),
          u γ ≤
          A * B) :
    Xroot T u = Xgeom T u termTube + Xdup T u termTube ∧
      Xdup T u termTube ≤ (m : ℝ) * (A * B) * (∑ γ ∈ treeLeaves T, u γ) := by
  -- Part 1: Xroot splits exactly into Xgeom + Xdup.
  have hsplit : Xroot T u = Xgeom T u termTube + Xdup T u termTube := by
    simp only [Xroot, Xgeom, Xdup, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun γ' _ => ?_
    by_cases hlca : treeLCA γ γ' = []
    · by_cases htube : termTube γ = termTube γ'
      · simp [hlca, htube]
      · simp [hlca, htube]
    · simp [hlca]
  -- Part 2: the duplicate bound.
  have hbound :
      Xdup T u termTube ≤ (m : ℝ) * (A * B) * (∑ γ ∈ treeLeaves T, u γ) := by
    -- Step 1: dropping the root-cross condition can only increase the sum,
    -- since all summands are nonnegative on leaves.
    have hdrop : Xdup T u termTube
        ≤ ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
            (if termTube γ = termTube γ' then u γ * u γ' else 0) := by
      simp only [Xdup]
      refine Finset.sum_le_sum fun γ hγ => Finset.sum_le_sum fun γ' hγ' => ?_
      by_cases h : treeLCA γ γ' = [] ∧ termTube γ = termTube γ'
      · rw [if_pos h, if_pos h.2]
      · rw [if_neg h]
        by_cases ht : termTube γ = termTube γ'
        · rw [if_pos ht]
          exact mul_nonneg (hu γ hγ) (hu γ' hγ')
        · rw [if_neg ht]
    -- Step 2: fiber the double sum over terminal tubes.
    have hinner : ∀ γ ∈ treeLeaves T,
        (∑ γ' ∈ treeLeaves T, (if termTube γ = termTube γ' then u γ * u γ' else 0))
          = ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = termTube γ),
              u γ * u γ' := by
      intro γ _
      have hpt : ∀ γ' ∈ treeLeaves T,
          (if termTube γ = termTube γ' then u γ * u γ' else 0)
            = (if termTube γ' = termTube γ then u γ * u γ' else 0) := by
        intro γ' _
        by_cases h : termTube γ = termTube γ'
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun h' => h h'.symm)]
      rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter]
    have hfiber : (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
            (if termTube γ = termTube γ' then u γ * u γ' else 0))
        = ∑ t : Fin n,
            (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ) ^ 2 := by
      have step1 : (∑ γ ∈ treeLeaves T, ∑ γ' ∈ (treeLeaves T).filter
              (fun γ' => termTube γ' = termTube γ), u γ * u γ')
          = ∑ t : Fin n, ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
              ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = termTube γ),
                u γ * u γ' :=
        (Finset.sum_fiberwise_of_maps_to (g := termTube) (fun x _ => Finset.mem_univ _)
          (fun γ => ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = termTube γ),
            u γ * u γ')).symm
      have step2 : (∑ t : Fin n, ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
              ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = termTube γ),
                u γ * u γ')
          = ∑ t : Fin n, ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
              ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t),
                u γ * u γ' := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun γ hγ => ?_
        have hteq : termTube γ = t := (Finset.mem_filter.mp hγ).2
        rw [hteq]
      have step3 : (∑ t : Fin n, ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t),
              ∑ γ' ∈ (treeLeaves T).filter (fun γ' => termTube γ' = t),
                u γ * u γ')
          = ∑ t : Fin n,
              (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ) ^ 2 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [pow_two]
        exact (Finset.sum_mul_sum _ _ _ _).symm
      rw [Finset.sum_congr rfl (fun γ hγ => hinner γ hγ), step1, step2, step3]
    -- Step 3: per-tube estimate from the carrier aggregate hypothesis.
    have htube : ∀ t : Fin n,
        (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ) ^ 2
          ≤ (m : ℝ) * (A * B)
              * (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ) := by
      intro t
      have hnn : 0 ≤ ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ :=
        Finset.sum_nonneg fun γ hγ => hu γ (Finset.mem_filter.mp hγ).1
      have hle :
          (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ)
            ≤ (m : ℝ) * (A * B) := by
        have hfib : (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ)
            = ∑ c : Fin m, ∑ γ ∈ ((treeLeaves T).filter (fun γ => termTube γ = t)).filter
                (fun γ => carrier γ = c), u γ :=
          (Finset.sum_fiberwise_of_maps_to (g := carrier) (fun x _ => Finset.mem_univ _)
            (fun γ => u γ)).symm
        rw [hfib]
        calc (∑ c : Fin m, ∑ γ ∈ ((treeLeaves T).filter (fun γ => termTube γ = t)).filter
                (fun γ => carrier γ = c), u γ)
            ≤ ∑ _c : Fin m, A * B := by
              refine Finset.sum_le_sum fun c _ => ?_
              have hff : ((treeLeaves T).filter (fun γ => termTube γ = t)).filter
                    (fun γ => carrier γ = c)
                  = (treeLeaves T).filter (fun γ => termTube γ = t ∧ carrier γ = c) :=
                Finset.filter_filter _ _ _
              rw [hff]
              exact hagg t c
          _ = (m : ℝ) * (A * B) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ) ^ 2
          = (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ)
            * (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ) :=
            pow_two _
        _ ≤ (m : ℝ) * (A * B)
              * (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ) :=
            mul_le_mul_of_nonneg_right hle hnn
    -- Assemble the chain.
    have hfact : (∑ t : Fin n, (m : ℝ) * (A * B)
          * (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ))
        = (m : ℝ) * (A * B)
          * (∑ t : Fin n, ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ) :=
      (Finset.mul_sum _ _ _).symm
    have hfib3 : (∑ t : Fin n, ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ)
        = ∑ γ ∈ treeLeaves T, u γ :=
      Finset.sum_fiberwise_of_maps_to (g := termTube) (fun x _ => Finset.mem_univ _)
        (fun γ => u γ)
    calc Xdup T u termTube
        ≤ ∑ t : Fin n,
            (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ) ^ 2 :=
          hdrop.trans hfiber.le
      _ ≤ ∑ t : Fin n, (m : ℝ) * (A * B)
            * (∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), u γ) :=
          Finset.sum_le_sum fun t _ => htube t
      _ = (m : ℝ) * (A * B) * (∑ γ ∈ treeLeaves T, u γ) := by
          rw [hfact, hfib3]
  exact ⟨hsplit, hbound⟩

end FilteredDescent
