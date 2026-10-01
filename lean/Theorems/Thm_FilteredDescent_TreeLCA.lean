import Definitions.Def_FilteredDescent_Tree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# M5 — History-tree LCA reduction (paper (131)–(141))

Splitting the leaf-pair sum by least common ancestor: pairs whose LCA is
the root give `X^{root}`; pairs whose LCA is a proper node `a` are
controlled by the induction invariant `W_a ≤ B`, and each level of the
tree contributes at most `B · N`.  With tree height `≤ D` (the finite form
of the paper's `H_{I,k} = δ^{-o(1)}` subpower height factor),

  `∫N² ≤ D · B · ∫N + X^{root}`.
-/

namespace FilteredDescent

/-- The LCA is a prefix of the first history (`take` is always a prefix). -/
lemma lca_prefix_left {α : Type} [DecidableEq α] (γ γ' : List α) :
    treeLCA γ γ' <+: γ := by
  unfold treeLCA
  exact List.take_prefix _ γ

/-- The LCA is a prefix of the second history (it is chosen among the
common prefixes via `max'`). -/
lemma lca_prefix_right {α : Type} [DecidableEq α] (γ γ' : List α) :
    treeLCA γ γ' <+: γ' := by
  have h0 : (0 : ℕ) ∈ (Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ') :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.succ_pos _), List.nil_prefix⟩
  have hmem := Finset.max'_mem _ ⟨0, h0⟩
  rw [Finset.mem_filter] at hmem
  have heq : treeLCA γ γ' = γ.take (((Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ')).max' ⟨0, h0⟩) := rfl
  rw [heq]
  exact hmem.2

/-- A prefix of `γ` is recovered by taking its length. -/
lemma prefix_eq_take {α : Type} {γ a : List α} (h : a <+: γ) :
    a = γ.take a.length := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append]
  simp

/-- Product of indicator-weighted terms as a joint indicator. -/
lemma if_and_mul {α : Type} [DecidableEq α] (a γ γ' : List α) (x y : ℝ) :
    (if a <+: γ then x else 0) * (if a <+: γ' then y else 0)
      = if a <+: γ ∧ a <+: γ' then x * y else 0 := by
  by_cases h1 : a <+: γ <;> by_cases h2 : a <+: γ' <;> simp [h1, h2]

theorem tree_lca_reduction {α : Type} [DecidableEq α]
    (T : Finset (List α))
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (u : List α → ℝ) (hu : ∀ γ ∈ treeLeaves T, 0 ≤ u γ)
    (B : ℝ) (hB : 0 ≤ B)
    (D : ℕ)
    (hproper : ∀ a ∈ T, a ≠ [] → nodeAgg T u a ≤ B)
    (hheight : ∀ a ∈ T, a.length ≤ D) :
    (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T, u γ * u γ')
      ≤ (D : ℝ) * B * (∑ γ ∈ treeLeaves T, u γ) + Xroot T u := by
  have hsub : treeLeaves T ⊆ T := Finset.filter_subset _ _
  -- Remainder term: leaf pairs whose LCA is a proper (non-root) node.
  set R : ℝ := ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
    if treeLCA γ γ' ≠ [] then u γ * u γ' else 0 with hR
  -- Node aggregates are nonnegative.
  have hWnn : ∀ a : List α, 0 ≤ nodeAgg T u a := by
    intro a
    simp only [nodeAgg]
    apply Finset.sum_nonneg
    intro γ hγ
    split_ifs with h
    · exact hu γ hγ
    · exact le_refl 0
  -- Step 1+2: S^2 = Xroot + R (terms with LCA = [] give Xroot).
  have hS2 : (∑ γ ∈ treeLeaves T, u γ) ^ 2 = Xroot T u + R := by
    have hsplit : ∀ γ ∈ treeLeaves T, ∀ γ' ∈ treeLeaves T,
        u γ * u γ'
          = (if treeLCA γ γ' = [] then u γ * u γ' else 0)
            + (if treeLCA γ γ' ≠ [] then u γ * u γ' else 0) := by
      intro γ _ γ' _
      by_cases h : treeLCA γ γ' = []
      · rw [if_pos h, if_neg (not_not.mpr h), add_zero]
      · rw [if_neg h, if_pos h, zero_add]
    rw [sq, Finset.sum_mul_sum]
    unfold Xroot
    rw [hR, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro γ' hγ'
    exact hsplit γ hγ γ' hγ'
  -- Step 3a: each non-root-LCA pair is covered by its LCA node `a₀`.
  have hpair : ∀ γ ∈ treeLeaves T, ∀ γ' ∈ treeLeaves T,
      (if treeLCA γ γ' ≠ [] then u γ * u γ' else 0)
        ≤ ∑ a ∈ T.filter (· ≠ []),
            (if a <+: γ ∧ a <+: γ' then u γ * u γ' else 0) := by
    intro γ hγ γ' hγ'
    have hnn : 0 ≤ u γ * u γ' := mul_nonneg (hu γ hγ) (hu γ' hγ')
    have htermnn : ∀ a ∈ T.filter (· ≠ []),
        0 ≤ (if a <+: γ ∧ a <+: γ' then u γ * u γ' else 0) := by
      intro a _
      split_ifs with h
      · exact hnn
      · exact le_refl 0
    by_cases h : treeLCA γ γ' ≠ []
    · rw [if_pos h]
      have ha₀T : treeLCA γ γ' ∈ T :=
        hprefix γ (hsub hγ) _ (lca_prefix_left γ γ')
      have ha₀ : treeLCA γ γ' ∈ T.filter (· ≠ []) :=
        Finset.mem_filter.mpr ⟨ha₀T, h⟩
      have hle : (if treeLCA γ γ' <+: γ ∧ treeLCA γ γ' <+: γ'
            then u γ * u γ' else 0)
          ≤ ∑ a ∈ T.filter (· ≠ []),
              (if a <+: γ ∧ a <+: γ' then u γ * u γ' else 0) :=
        Finset.single_le_sum htermnn ha₀
      rw [if_pos ⟨lca_prefix_left γ γ', lca_prefix_right γ γ'⟩] at hle
      exact hle
    · rw [if_neg h]
      exact Finset.sum_nonneg htermnn
  -- Step 3b: W_a^2 expanded as a double sum over leaf pairs.
  have hW2 : ∀ a ∈ T.filter (· ≠ []),
      (nodeAgg T u a) ^ 2
        = ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
            (if a <+: γ ∧ a <+: γ' then u γ * u γ' else 0) := by
    intro a _
    rw [sq]
    simp only [nodeAgg]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    apply Finset.sum_congr rfl
    intro γ' _
    exact if_and_mul a γ γ' (u γ) (u γ')
  -- Swap the order of summation.
  have hswap : (∑ a ∈ T.filter (· ≠ []), ∑ γ ∈ treeLeaves T,
          ∑ γ' ∈ treeLeaves T,
          (if a <+: γ ∧ a <+: γ' then u γ * u γ' else 0))
      = ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T, ∑ a ∈ T.filter (· ≠ []),
          (if a <+: γ ∧ a <+: γ' then u γ * u γ' else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ _
    exact Finset.sum_comm
  -- Step 3c: R ≤ ∑_{a≠[]} W_a^2.
  have hRbound : R ≤ ∑ a ∈ T.filter (· ≠ []), (nodeAgg T u a) ^ 2 := by
    have e1 : (∑ a ∈ T.filter (· ≠ []), (nodeAgg T u a) ^ 2)
        = ∑ a ∈ T.filter (· ≠ []), ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
            (if a <+: γ ∧ a <+: γ' then u γ * u γ' else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hW2 a ha
    rw [hR, e1, hswap]
    apply Finset.sum_le_sum
    intro γ hγ
    apply Finset.sum_le_sum
    intro γ' hγ'
    exact hpair γ hγ γ' hγ'
  -- Step 4: ∑ W_a^2 ≤ B * ∑ W_a (using W_a ≤ B and W_a ≥ 0).
  have hW2B : ∑ a ∈ T.filter (· ≠ []), (nodeAgg T u a) ^ 2
      ≤ B * ∑ a ∈ T.filter (· ≠ []), nodeAgg T u a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hproper a ha.1 ha.2) (hWnn a)
  -- Step 5a: each leaf has at most D nontrivial prefixes in T.
  have hcard : ∀ γ ∈ treeLeaves T,
      (T.filter (fun a => a ≠ [] ∧ a <+: γ)).card ≤ D := by
    intro γ hγ
    have hγT : γ ∈ T := hsub hγ
    have hinj : Set.InjOn List.length
        (↑(T.filter (fun a => a ≠ [] ∧ a <+: γ)) : Set (List α)) := by
      intro a ha b hb hb_len
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
      obtain ⟨_, _, hpre_a⟩ := ha
      obtain ⟨_, _, hpre_b⟩ := hb
      rw [prefix_eq_take hpre_a, prefix_eq_take hpre_b, hb_len]
    have himg : (T.filter (fun a => a ≠ [] ∧ a <+: γ)).image List.length
        ⊆ Finset.Icc 1 (γ.length) := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      rw [Finset.mem_filter] at ha
      obtain ⟨_, hane, hpre⟩ := ha
      rw [Finset.mem_Icc]
      refine ⟨?_, List.IsPrefix.length_le hpre⟩
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      exact hane (List.eq_nil_of_length_eq_zero h0)
    have h1 : (T.filter (fun a => a ≠ [] ∧ a <+: γ)).card
        = ((T.filter (fun a => a ≠ [] ∧ a <+: γ)).image List.length).card :=
      (Finset.card_image_of_injOn hinj).symm
    calc (T.filter (fun a => a ≠ [] ∧ a <+: γ)).card
          = ((T.filter (fun a => a ≠ [] ∧ a <+: γ)).image List.length).card := h1
      _ ≤ (Finset.Icc 1 (γ.length)).card := Finset.card_le_card himg
      _ = γ.length := by rw [Nat.card_Icc]; omega
      _ ≤ D := hheight γ hγT
  -- Step 5b: ∑_{a≠[]} W_a ≤ D * S.
  have hWsum : ∑ a ∈ T.filter (· ≠ []), nodeAgg T u a
      ≤ (D : ℝ) * ∑ γ ∈ treeLeaves T, u γ := by
    have e1 : (∑ a ∈ T.filter (· ≠ []), nodeAgg T u a)
        = ∑ γ ∈ treeLeaves T, ∑ a ∈ T.filter (· ≠ []),
            (if a <+: γ then u γ else 0) := by
      simp only [nodeAgg]
      exact Finset.sum_comm
    have hset : ∀ γ : List α, (T.filter (· ≠ [])).filter (fun a => a <+: γ)
        = T.filter (fun a => a ≠ [] ∧ a <+: γ) := by
      intro γ
      ext a
      simp only [Finset.mem_filter, and_assoc]
    rw [e1, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ hγ
    have e2 : (∑ a ∈ T.filter (· ≠ []), (if a <+: γ then u γ else 0))
        = ((T.filter (fun a => a ≠ [] ∧ a <+: γ)).card : ℝ) * u γ := by
      rw [← Finset.sum_filter, hset γ, Finset.sum_const, nsmul_eq_mul]
    rw [e2]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard γ hγ)) (hu γ hγ)
  -- Assemble: R ≤ D * B * S.
  have hRle : R ≤ (D : ℝ) * B * ∑ γ ∈ treeLeaves T, u γ := by
    calc R ≤ ∑ a ∈ T.filter (· ≠ []), (nodeAgg T u a) ^ 2 := hRbound
      _ ≤ B * ∑ a ∈ T.filter (· ≠ []), nodeAgg T u a := hW2B
      _ ≤ B * ((D : ℝ) * ∑ γ ∈ treeLeaves T, u γ) :=
          mul_le_mul_of_nonneg_left hWsum hB
      _ = (D : ℝ) * B * ∑ γ ∈ treeLeaves T, u γ := by
        rw [mul_left_comm, mul_assoc]
  have hLHS : (∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T, u γ * u γ')
      = (∑ γ ∈ treeLeaves T, u γ) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  rw [hLHS, hS2]
  calc Xroot T u + R
      ≤ Xroot T u + (↑D * B * ∑ γ ∈ treeLeaves T, u γ) := add_le_add_right hRle _
    _ = ↑D * B * ∑ γ ∈ treeLeaves T, u γ + Xroot T u := add_comm _ _

end FilteredDescent
