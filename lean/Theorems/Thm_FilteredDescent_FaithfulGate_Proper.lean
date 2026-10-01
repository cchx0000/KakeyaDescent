import Theorems.Thm_FilteredDescent_FaithfulGate_Defs
import Theorems.Thm_FilteredDescent_FaithfulGate_LCA
import Definitions.Def_FilteredDescent_Tree
import Definitions.Def_FilteredDescent_Subpower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

/-!
# Faithful root-cross gate — proper-predecessor recombination (paper §10, (139)→(141))

The proper-predecessor recombination bound.  Paper (139): proper nodes at a
single depth have disjoint descendant sets, so their node aggregates
`W_a = Σ_{γ ∈ Desc(a)} u_γ` sum to at most the total leaf load.
Paper (141): summing the pair mass `Σ_{LCA(γ,γ') = a} u_γ u_γ' ≤ W_a ^ 2`
over all proper nodes `a ≠ r∗`, and using the predecessor invariance
`W_a ≤ B^pred` (paper (138), taken here as the explicit hypothesis
`Hpred`, proved by a parallel induction stream), gives

  `Σ_{LCA(γ,γ')≠r∗} u_γ u_γ' ≤ B^pred · (D+1) · N`,

where `D` is the tree depth and `N` the total leaf load.  All statements
are for general prefix-closed trees — no toy instances.
-/

namespace FilteredDescent

/-- Node aggregates are nonnegative for nonnegative leaf loads. -/
theorem nodeAgg_nonneg {α : Type} [DecidableEq α] (T : Finset (List α))
    (u : List α → ℝ) (hu : ∀ γ ∈ treeLeaves T, 0 ≤ u γ) (a : List α) :
    0 ≤ nodeAgg T u a := by
  unfold nodeAgg
  apply Finset.sum_nonneg
  intro γ hγ
  apply ite_nonneg
  · exact hu γ hγ
  · exact le_refl 0

/-- Auxiliary form of `proper_pair_le_Wsq` for a general nonnegative leaf
weight `u`: the pair mass over leaves with `LCA = a` is at most `W_a ^ 2`. -/
private theorem pair_le_WSq_aux {α : Type} [DecidableEq α]
    (T : Finset (List α)) (u : List α → ℝ)
    (hu : ∀ γ ∈ treeLeaves T, 0 ≤ u γ) (a : List α) :
    ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
      (if treeLCA γ γ' = a then u γ * u γ' else 0)
      ≤ (nodeAgg T u a) ^ 2 := by
  have hsq : (nodeAgg T u a) ^ 2
      = ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
        (if a <+: γ then u γ else 0) * (if a <+: γ' then u γ' else 0) := by
    unfold nodeAgg
    rw [pow_two, ← Finset.sum_mul_sum]
  rw [hsq]
  apply Finset.sum_le_sum
  intro γ hγ
  apply Finset.sum_le_sum
  intro γ' hγ'
  by_cases h : treeLCA γ γ' = a
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := treeLCA_eq_imp_prefix h
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h]
    by_cases h1 : a <+: γ <;> by_cases h2 : a <+: γ'
    · rw [if_pos h1, if_pos h2]
      exact mul_nonneg (hu γ hγ) (hu γ' hγ')
    · rw [if_pos h1, if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
    · rw [if_neg h1, zero_mul]

/-- The pair mass over leaves with `LCA = a` is at most `W_a ^ 2`. -/
theorem proper_pair_le_Wsq {α : Type} [DecidableEq α]
    (T : Finset (List α)) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (a : List α) :
    ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
      (if treeLCA γ γ' = a then load γ δ * load γ' δ else 0)
      ≤ (nodeAgg T (fun γ => load γ δ) a) ^ 2 :=
  pair_le_WSq_aux T (fun γ => load γ δ)
    (fun γ hγ => hload γ hγ δ hδ0 hδ1) a

/-- Paper (139): proper nodes at one depth have disjoint descendant sets, so
their aggregates sum to at most the total leaf load.  Two distinct depth-`d`
nodes prefixing one leaf must both equal the leaf's length-`d` take. -/
theorem depth_sum_le {α : Type} [DecidableEq α] (T : Finset (List α))
    (d : ℕ) (u : List α → ℝ) (hu : ∀ γ ∈ treeLeaves T, 0 ≤ u γ) :
    ∑ a ∈ T.filter (fun a => a ≠ [] ∧ a.length = d), nodeAgg T u a
      ≤ ∑ γ ∈ treeLeaves T, u γ := by
  unfold nodeAgg
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro γ hγ
  have hstep : (∑ a ∈ T.filter (fun a => a ≠ [] ∧ a.length = d),
        (if a <+: γ then u γ else 0))
      = ((T.filter (fun a => a ≠ [] ∧ a.length = d)).filter
        (fun a => a <+: γ)).card • u γ := by
    rw [← Finset.sum_filter]
    exact Finset.sum_const _
  rw [hstep, nsmul_eq_mul]
  have hcard : ((T.filter (fun a => a ≠ [] ∧ a.length = d)).filter
      (fun a => a <+: γ)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨haT, ha_pre⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbT, hb_pre⟩ := Finset.mem_filter.mp hb
    obtain ⟨-, ha_len⟩ := (Finset.mem_filter.mp haT).2
    obtain ⟨-, hb_len⟩ := (Finset.mem_filter.mp hbT).2
    have h1 : a = γ.take a.length := List.prefix_iff_eq_take.mp ha_pre
    have h2 : b = γ.take b.length := List.prefix_iff_eq_take.mp hb_pre
    rw [h1, h2, ha_len, hb_len]
  calc ((((T.filter (fun a => a ≠ [] ∧ a.length = d)).filter
        (fun a => a <+: γ)).card : ℕ) : ℝ) * u γ
        ≤ 1 * u γ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hu γ hγ)
      _ = u γ := one_mul _

/-- Paper (141): the proper-predecessor recombination bound.
`Hpred` is the predecessor invariance (paper (138)), taken as an explicit
hypothesis proved by a parallel induction stream. -/
theorem proper_predecessor_bound {α : Type} [DecidableEq α]
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Bpred : ℝ → ℝ)
    (hBpred : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (Hpred : ∀ a ∈ T, a ≠ [] → nodeAgg T (fun γ => load γ δ) a ≤ Bpred δ) :
    ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
      (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0)
      ≤ Bpred δ * (((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ)
        * totalLoad T load δ) := by
  -- (a) Reorganize the pair sum by LCA value.
  have hinner : ∀ γ ∈ treeLeaves T, ∀ γ' ∈ treeLeaves T,
      (∑ a ∈ T.filter (fun a => a ≠ []),
        (if treeLCA γ γ' = a then load γ δ * load γ' δ else 0))
        = (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0) := by
    intro γ hγ γ' hγ'
    by_cases h : treeLCA γ γ' ≠ []
    · rw [if_pos h]
      have hmem : treeLCA γ γ' ∈ T.filter (fun a => a ≠ []) := by
        rw [Finset.mem_filter]
        exact ⟨treeLCA_mem_tree hprefix (Finset.mem_of_mem_filter γ hγ)
          (Finset.mem_of_mem_filter γ' hγ'), h⟩
      rw [Finset.sum_ite_eq _ _ (fun _ => load γ δ * load γ' δ), if_pos hmem]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_filter] at ha
      have hne : treeLCA γ γ' ≠ a := by
        intro hcon
        rw [← hcon] at ha
        exact h ha.2
      rw [if_neg hne]
  have hreorg : (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
        (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0))
      = ∑ a ∈ T.filter (fun a => a ≠ []), ∑ γ ∈ treeLeaves T,
        ∑ γ' ∈ treeLeaves T,
          (if treeLCA γ γ' = a then load γ δ * load γ' δ else 0) := by
    calc ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
            (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0)
        = ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
            ∑ a ∈ T.filter (fun a => a ≠ []),
            (if treeLCA γ γ' = a then load γ δ * load γ' δ else 0) := by
          apply Finset.sum_congr rfl
          intro γ hγ
          apply Finset.sum_congr rfl
          intro γ' hγ'
          exact (hinner γ hγ γ' hγ').symm
      _ = ∑ a ∈ T.filter (fun a => a ≠ []), ∑ γ ∈ treeLeaves T,
            ∑ γ' ∈ treeLeaves T,
            (if treeLCA γ γ' = a then load γ δ * load γ' δ else 0) := by
          have hswap : ∀ γ ∈ treeLeaves T,
              (∑ γ' ∈ treeLeaves T, ∑ a ∈ T.filter (fun a => a ≠ []),
                (if treeLCA γ γ' = a then load γ δ * load γ' δ else 0))
              = ∑ a ∈ T.filter (fun a => a ≠ []), ∑ γ' ∈ treeLeaves T,
                (if treeLCA γ γ' = a then load γ δ * load γ' δ else 0) :=
            fun γ _ => Finset.sum_comm
          rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
  -- (b) Each LCA fiber: `P_a ≤ W_a ^ 2 = W_a * W_a ≤ Bpred δ * W_a`.
  have hPa : ∀ a ∈ T.filter (fun a => a ≠ []),
      (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
        (if treeLCA γ γ' = a then load γ δ * load γ' δ else 0))
        ≤ Bpred δ * nodeAgg T (fun γ => load γ δ) a := by
    intro a ha
    rw [Finset.mem_filter] at ha
    have hW : 0 ≤ nodeAgg T (fun γ => load γ δ) a :=
      nodeAgg_nonneg T _ (fun γ hγ => hload γ hγ δ hδ0 hδ1) a
    calc ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
            (if treeLCA γ γ' = a then load γ δ * load γ' δ else 0)
        ≤ (nodeAgg T (fun γ => load γ δ) a) ^ 2 :=
          proper_pair_le_Wsq T load hload δ hδ0 hδ1 a
      _ = nodeAgg T (fun γ => load γ δ) a
          * nodeAgg T (fun γ => load γ δ) a := pow_two _
      _ ≤ nodeAgg T (fun γ => load γ δ) a * Bpred δ :=
          mul_le_mul_of_nonneg_left (Hpred a ha.1 ha.2) hW
      _ = Bpred δ * nodeAgg T (fun γ => load γ δ) a := mul_comm _ _
  -- (c) Sum over proper nodes, fibered by depth: each fiber ≤ N, and there
  -- are D+1 fibers.
  have hmaps : ∀ a ∈ T.filter (fun a => a ≠ []),
      List.length a ∈ Finset.range (T.sup' ⟨[], hroot⟩ List.length + 1) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_range]
    have hle : List.length a ≤ T.sup' ⟨[], hroot⟩ List.length :=
      Finset.le_sup' List.length ha.1
    omega
  have hfib : ∀ d ∈ Finset.range (T.sup' ⟨[], hroot⟩ List.length + 1),
      (∑ a ∈ (T.filter (fun a => a ≠ [])).filter (fun a => List.length a = d),
        nodeAgg T (fun γ => load γ δ) a) ≤ totalLoad T load δ := by
    intro d _
    rw [Finset.filter_filter]
    exact depth_sum_le T d (fun γ => load γ δ)
      (fun γ hγ => hload γ hγ δ hδ0 hδ1)
  have hsum : ∑ a ∈ T.filter (fun a => a ≠ []), nodeAgg T (fun γ => load γ δ) a
      ≤ ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ)
        * totalLoad T load δ := by
    have hfib_eq : (∑ a ∈ T.filter (fun a => a ≠ []),
          nodeAgg T (fun γ => load γ δ) a)
        = ∑ d ∈ Finset.range (T.sup' ⟨[], hroot⟩ List.length + 1),
          ∑ a ∈ (T.filter (fun a => a ≠ [])).filter (fun a => List.length a = d),
            nodeAgg T (fun γ => load γ δ) a :=
      (Finset.sum_fiberwise_of_maps_to (g := List.length)
        (t := Finset.range (T.sup' ⟨[], hroot⟩ List.length + 1)) hmaps _).symm
    rw [hfib_eq]
    calc ∑ d ∈ Finset.range (T.sup' ⟨[], hroot⟩ List.length + 1),
            ∑ a ∈ (T.filter (fun a => a ≠ [])).filter
              (fun a => List.length a = d),
            nodeAgg T (fun γ => load γ δ) a
        ≤ ∑ d ∈ Finset.range (T.sup' ⟨[], hroot⟩ List.length + 1),
            totalLoad T load δ :=
          Finset.sum_le_sum (fun d hd => hfib d hd)
      _ = ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ)
            * totalLoad T load δ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Combine.
  calc ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
          (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0)
      = ∑ a ∈ T.filter (fun a => a ≠ []), ∑ γ ∈ treeLeaves T,
          ∑ γ' ∈ treeLeaves T,
          (if treeLCA γ γ' = a then load γ δ * load γ' δ else 0) := hreorg
    _ ≤ ∑ a ∈ T.filter (fun a => a ≠ []),
          Bpred δ * nodeAgg T (fun γ => load γ δ) a :=
          Finset.sum_le_sum hPa
    _ = Bpred δ * ∑ a ∈ T.filter (fun a => a ≠ []),
          nodeAgg T (fun γ => load γ δ) a :=
          (Finset.mul_sum _ _ _).symm
    _ ≤ Bpred δ * ((((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ))
          * totalLoad T load δ) :=
          mul_le_mul_of_nonneg_left hsum (hBpred δ hδ0 hδ1)

/-- Paper (141) as a subpower bound: the proper-predecessor pair mass is
`≲ Bpred δ * N δ` with constant `D+1`. -/
theorem proper_predecessor_SubpowerLE {α : Type} [DecidableEq α]
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (hBpred : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (Hpred : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ a ∈ T, a ≠ [] →
      nodeAgg T (fun γ => load γ δ) a ≤ Bpred δ) :
    SubpowerLE
      (fun δ => ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
        (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0))
      (fun δ => Bpred δ * totalLoad T load δ) := by
  intro ε hε
  refine ⟨((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ), by positivity,
    fun δ hδ0 hδ1 => ?_⟩
  have h4 := proper_predecessor_bound T hroot hprefix load hload δ hδ0 hδ1
    Bpred hBpred (Hpred δ hδ0 hδ1)
  have h1 : (1 : ℝ) ≤ δ ^ (-ε) := by
    rw [Real.rpow_neg (le_of_lt hδ0)]
    exact (one_le_inv_iff₀).mpr ⟨Real.rpow_pos_of_pos hδ0 ε,
      le_of_lt (Real.rpow_lt_one (le_of_lt hδ0) hδ1 hε)⟩
  have hnn : 0 ≤ Bpred δ * totalLoad T load δ :=
    mul_nonneg (hBpred δ hδ0 hδ1) (totalLoad_nonneg T load hload δ hδ0 hδ1)
  have hDnn : (0 : ℝ) ≤ ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ) := by
    positivity
  have hle : Bpred δ * totalLoad T load δ
      ≤ δ ^ (-ε) * (Bpred δ * totalLoad T load δ) := by
    calc Bpred δ * totalLoad T load δ
        = 1 * (Bpred δ * totalLoad T load δ) := by ring
      _ ≤ δ ^ (-ε) * (Bpred δ * totalLoad T load δ) :=
          mul_le_mul_of_nonneg_right h1 hnn
  calc (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
          (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0))
      ≤ Bpred δ * ((((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ))
          * totalLoad T load δ) := h4
    _ = ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ)
          * (Bpred δ * totalLoad T load δ) := by ring
    _ ≤ ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ)
          * (δ ^ (-ε) * (Bpred δ * totalLoad T load δ)) :=
          mul_le_mul_of_nonneg_left hle hDnn
    _ = ((T.sup' ⟨[], hroot⟩ List.length + 1 : ℕ) : ℝ) * δ ^ (-ε)
          * (Bpred δ * totalLoad T load δ) := by ring

end FilteredDescent
