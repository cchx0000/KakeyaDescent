import Definitions.Def_FilteredDescent_Tree
import Definitions.Def_FilteredDescent_Subpower
import Theorems.Thm_FilteredDescent_FaithfulGate_Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

/-!
# Filtered descent — re-rooted subtrees and the division lemma (paper §10.1)

For the well-founded descent (Stream D, M3), the induction step at a
vertex `a₀` applies the root-cross gate to the *descent subtree* rooted
at `a₀`: the histories below `a₀`, reindexed so the new root is `[]`.
This file provides:

* `reroot T a₀`: the re-rooted subtree, with `[]` as root
  (`reroot_root`), prefix-closed (`reroot_prefix`).
* Correspondence of leaves (`reroot_leaves`, `reroot_leaf_lift`,
  `reroot_leaf_descend`), of the least common ancestor relative to `a₀`
  (`reroot_treeLCA`), and of node aggregates (`reroot_nodeAgg`) and the
  total load (`reroot_totalLoad`).
* `SubpowerLE.div_of_sq`: the division lemma — `x² ≲ B·x` implies
  `x ≲ B` for nonnegative `x`, `B`.  This is the paper's division of the
  descent-step output `N(δ)² ≲ B^pred(δ)·N(δ)` by `N(δ)`.
* `SubpowerLE.of_pointwise_le`: pointwise domination implies subpower
  domination (for nonnegative right-hand side); used for the leaf case.

All proofs are real; no sorry/axiom.
-/

namespace FilteredDescent

/-- Re-rooted subtree at `a₀`: descendant histories reindexed relative
to `a₀`, so the new root is `[]`.  Paper §10.1: the descent subtree
rooted at a proper vertex, on which the gate is applied inductively. -/
def reroot {α : Type} [DecidableEq α] (T : Finset (List α)) (a₀ : List α) :
    Finset (List α) :=
  (T.filter (fun l => a₀ <+: l)).image (fun l => l.drop a₀.length)

theorem reroot_mem {α : Type} [DecidableEq α] (T : Finset (List α))
    (a₀ s : List α) :
    s ∈ reroot T a₀ ↔ ∃ l ∈ T, a₀ <+: l ∧ l.drop a₀.length = s := by
  unfold reroot
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨l, ⟨hlT, hal⟩, hls⟩
    exact ⟨l, hlT, hal, hls⟩
  · rintro ⟨l, hlT, hal, hls⟩
    exact ⟨l, ⟨hlT, hal⟩, hls⟩

/-- Reassembling a word from a prefix and its drop. -/
theorem append_drop_of_prefix {α : Type} {a₀ γ : List α} (h : a₀ <+: γ) :
    a₀ ++ γ.drop a₀.length = γ := by
  obtain ⟨u, hu⟩ := h
  conv_lhs => rw [← hu]
  rw [List.drop_left, hu]

/-- Dropping a common prefix preserves the prefix relation. -/
theorem prefix_drop_of_prefix {α : Type} {a₀ l γ : List α}
    (hal : a₀ <+: l) (hlγ : l <+: γ) :
    l.drop a₀.length <+: γ.drop a₀.length := by
  obtain ⟨u, hu⟩ := hal
  obtain ⟨t, ht⟩ := hlγ
  have h1 : l.drop a₀.length = u := by rw [← hu, List.drop_left]
  have h2 : γ.drop a₀.length = u ++ t := by
    have he : γ = a₀ ++ (u ++ t) := by rw [← ht, ← hu, List.append_assoc]
    rw [he, List.drop_left]
  rw [h1, h2]
  exact ⟨t, rfl⟩

theorem reroot_root {α : Type} [DecidableEq α] (T : Finset (List α))
    (a₀ : List α) (ha₀ : a₀ ∈ T) : [] ∈ reroot T a₀ := by
  rw [reroot_mem]
  exact ⟨a₀, ha₀, ⟨[], by simp⟩, List.drop_length⟩

theorem reroot_prefix {α : Type} [DecidableEq α] (T : Finset (List α))
    (a₀ : List α)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    {s p : List α} (hs : s ∈ reroot T a₀) (hps : p <+: s) :
    p ∈ reroot T a₀ := by
  rw [reroot_mem] at hs ⊢
  obtain ⟨l, hlT, hal, hls⟩ := hs
  obtain ⟨t, ht⟩ := hps
  have hl_eq : l = a₀ ++ l.drop a₀.length := (append_drop_of_prefix hal).symm
  refine ⟨a₀ ++ p, hprefix l hlT _ ?_, ⟨p, rfl⟩, List.drop_left⟩
  rw [hl_eq, hls]
  exact ⟨t, by rw [List.append_assoc, ht]⟩

theorem reroot_empty {α : Type} [DecidableEq α] (T : Finset (List α)) :
    reroot T [] = T := by
  ext s
  simp only [reroot_mem]
  constructor
  · rintro ⟨l, hlT, -, hls⟩
    simp at hls
    rw [← hls]
    exact hlT
  · intro hs
    exact ⟨s, hs, by simp, by simp⟩

/-- Every node of a finite prefix-closed tree extends to a leaf:
take an extension of maximal length. -/
theorem exists_leaf_extend {α : Type} [DecidableEq α] (T : Finset (List α))
    {l : List α} (hl : l ∈ T) : ∃ γ ∈ treeLeaves T, l <+: γ := by
  have hne : (T.filter (fun m => l <+: m)).Nonempty :=
    ⟨l, Finset.mem_filter.mpr ⟨hl, ⟨[], by simp⟩⟩⟩
  obtain ⟨m₀, hm₀S, hm₀max⟩ := Finset.exists_mem_eq_sup' hne List.length
  have hm₀T : m₀ ∈ T := (Finset.mem_filter.mp hm₀S).1
  have hm₀pre : l <+: m₀ := (Finset.mem_filter.mp hm₀S).2
  refine ⟨m₀, Finset.mem_filter.mpr ⟨hm₀T, ?_⟩, hm₀pre⟩
  intro l' hl' hpre
  have hl'S : l' ∈ T.filter (fun m => l <+: m) :=
    Finset.mem_filter.mpr ⟨hl', hm₀pre.trans hpre⟩
  have hle : l'.length ≤ m₀.length := by
    have h := Finset.le_sup' List.length hl'S
    rw [hm₀max] at h
    exact h
  obtain ⟨t, ht⟩ := hpre
  have ht0 : t = [] := by
    have hlen := congrArg List.length ht
    simp only [List.length_append] at hlen
    have h0 : t.length = 0 := by omega
    exact List.length_eq_zero_iff.mp h0
  rw [← ht, ht0, List.append_nil]

/-- Leaves of the re-rooted tree lift to leaves of the original tree. -/
theorem reroot_leaf_lift {α : Type} [DecidableEq α] (T : Finset (List α))
    (a₀ : List α)
    {s : List α} (hs : s ∈ treeLeaves (reroot T a₀)) :
    a₀ ++ s ∈ treeLeaves T := by
  unfold treeLeaves at hs
  rw [Finset.mem_filter] at hs
  obtain ⟨hsT, hsmax⟩ := hs
  rw [reroot_mem] at hsT
  obtain ⟨l, hlT, hal, hls⟩ := hsT
  obtain ⟨γ, hγleaf, hlγ⟩ := exists_leaf_extend T hlT
  have hγr : γ.drop a₀.length ∈ reroot T a₀ := by
    rw [reroot_mem]
    exact ⟨γ, (Finset.mem_filter.mp hγleaf).1, hal.trans hlγ, rfl⟩
  have hss : s <+: γ.drop a₀.length := by
    rw [← hls]
    exact prefix_drop_of_prefix hal hlγ
  have heq : γ.drop a₀.length = s := hsmax _ hγr hss
  have hγeq : a₀ ++ γ.drop a₀.length = γ := append_drop_of_prefix (hal.trans hlγ)
  rw [← heq, hγeq]
  exact hγleaf

/-- Prefix cancellation under a common prefix. -/
theorem append_prefix_append_iff {α : Type} {a₀ s₁ s₂ : List α} :
    (a₀ ++ s₁) <+: (a₀ ++ s₂) ↔ s₁ <+: s₂ := by
  constructor
  · rintro ⟨t, ht⟩
    have h : s₁ ++ t = s₂ := by
      have hc := congrArg (List.drop a₀.length) ht
      simp only [List.append_assoc, List.drop_left] at hc
      exact hc
    exact ⟨t, h⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [List.append_assoc, ht]⟩

/-- Leaves of the original tree below `a₀` descend to leaves of the
re-rooted tree. -/
theorem reroot_leaf_descend {α : Type} [DecidableEq α] (T : Finset (List α))
    (a₀ : List α)
    {γ : List α} (hγ : γ ∈ treeLeaves T) (haγ : a₀ <+: γ) :
    γ.drop a₀.length ∈ treeLeaves (reroot T a₀) := by
  unfold treeLeaves at hγ ⊢
  rw [Finset.mem_filter] at hγ ⊢
  obtain ⟨hγT, hγmax⟩ := hγ
  refine ⟨?_, ?_⟩
  · rw [reroot_mem]
    exact ⟨γ, hγT, haγ, rfl⟩
  · intro s' hs' hpre
    rw [reroot_mem] at hs'
    obtain ⟨l, hlT, hal, hls⟩ := hs'
    rw [← hls] at hpre
    have hγl : γ <+: l := by
      have e1 := append_drop_of_prefix haγ
      have e2 := append_drop_of_prefix hal
      rw [← e1, ← e2]
      exact append_prefix_append_iff.mpr hpre
    have heq : γ = l := (hγmax l hlT hγl).symm
    rw [← hls, heq]

/-- Leaf correspondence for re-rooting. -/
theorem reroot_leaves {α : Type} [DecidableEq α] (T : Finset (List α))
    (a₀ : List α) :
    treeLeaves (reroot T a₀)
      = ((treeLeaves T).filter (fun γ => a₀ <+: γ)).image
        (fun γ => γ.drop a₀.length) := by
  ext s
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · intro hs
    have hγ := reroot_leaf_lift T a₀ hs
    exact ⟨a₀ ++ s, ⟨hγ, ⟨s, rfl⟩⟩, List.drop_left⟩
  · rintro ⟨γ, ⟨hγ, haγ⟩, hdrop⟩
    rw [← hdrop]
    exact reroot_leaf_descend T a₀ hγ haγ

/-- Reindexing a leaf sum through the re-rooting. -/
theorem reroot_sum_leaves {α : Type} [DecidableEq α] (T : Finset (List α))
    (a₀ : List α)
    (F : List α → ℝ) :
    ∑ s ∈ treeLeaves (reroot T a₀), F s
      = ∑ γ ∈ (treeLeaves T).filter (fun γ => a₀ <+: γ),
        F (γ.drop a₀.length) := by
  rw [reroot_leaves T a₀, Finset.sum_image]
  · intro γ₁ hγ₁ γ₂ hγ₂ hdrop
    rw [Finset.mem_coe, Finset.mem_filter] at hγ₁ hγ₂
    have e1 := append_drop_of_prefix hγ₁.2
    have e2 := append_drop_of_prefix hγ₂.2
    have hdrop' : γ₁.drop a₀.length = γ₂.drop a₀.length := hdrop
    rw [← e1, ← e2, hdrop']

/-- Node-aggregate correspondence: the aggregate at `s` in the re-rooted
tree is the aggregate at `a₀ ++ s` in the original tree. -/
theorem reroot_nodeAgg {α : Type} [DecidableEq α] (T : Finset (List α))
    (a₀ : List α)
    (load : List α → ℝ → ℝ) (δ : ℝ) (s : List α) :
    nodeAgg (reroot T a₀) (fun s => load (a₀ ++ s) δ) s
      = nodeAgg T (fun γ => load γ δ) (a₀ ++ s) := by
  have h1 : nodeAgg (reroot T a₀) (fun s => load (a₀ ++ s) δ) s
      = ∑ γ ∈ (treeLeaves T).filter (fun γ => a₀ <+: γ),
        (if (a₀ ++ s) <+: γ then load γ δ else 0) := by
    unfold nodeAgg
    rw [reroot_sum_leaves T a₀
      (fun s' => if s <+: s' then load (a₀ ++ s') δ else 0)]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    have e := append_drop_of_prefix hγ.2
    show (if s <+: γ.drop a₀.length then load (a₀ ++ γ.drop a₀.length) δ else 0)
      = (if (a₀ ++ s) <+: γ then load γ δ else 0)
    by_cases h : (a₀ ++ s) <+: γ
    · rw [if_pos h]
      have hs : s <+: γ.drop a₀.length := by
        obtain ⟨t, ht⟩ := h
        have h2 : s ++ t = γ.drop a₀.length := by
          have hc := congrArg (List.drop a₀.length) ht
          simp only [List.append_assoc, List.drop_left] at hc
          exact hc
        exact ⟨t, h2⟩
      rw [if_pos hs, e]
    · rw [if_neg h]
      have hs : ¬ s <+: γ.drop a₀.length := by
        intro hcon
        apply h
        obtain ⟨t, ht⟩ := hcon
        exact ⟨t, by rw [List.append_assoc, ht, e]⟩
      rw [if_neg hs]
  have h2 : nodeAgg T (fun γ => load γ δ) (a₀ ++ s)
      = ∑ γ ∈ (treeLeaves T).filter (fun γ => a₀ <+: γ),
        (if (a₀ ++ s) <+: γ then load γ δ else 0) := by
    unfold nodeAgg
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro γ _
    show (if (a₀ ++ s) <+: γ then (fun γ => load γ δ) γ else 0)
      = (if a₀ <+: γ then (if (a₀ ++ s) <+: γ then load γ δ else 0) else 0)
    by_cases haγ : a₀ <+: γ
    · rw [if_pos haγ]
    · rw [if_neg haγ]
      have hcon : ¬ (a₀ ++ s) <+: γ := by
        intro h
        apply haγ
        obtain ⟨t, ht⟩ := h
        exact ⟨s ++ t, by rw [← List.append_assoc, ht]⟩
      rw [if_neg hcon]
  rw [h1, h2]

/-- Total-load correspondence: the total load of the re-rooted tree is
the node aggregate at `a₀`.  Paper (136) relativized: `W_{a₀} = N`. -/
theorem reroot_totalLoad {α : Type} [DecidableEq α] (T : Finset (List α))
    (a₀ : List α)
    (load : List α → ℝ → ℝ) (δ : ℝ) :
    totalLoad (reroot T a₀) (fun s δ => load (a₀ ++ s) δ) δ
      = nodeAgg T (fun γ => load γ δ) a₀ := by
  have h1 : totalLoad (reroot T a₀) (fun s δ => load (a₀ ++ s) δ) δ
      = ∑ γ ∈ (treeLeaves T).filter (fun γ => a₀ <+: γ), load γ δ := by
    unfold totalLoad
    rw [reroot_sum_leaves T a₀ (fun s => load (a₀ ++ s) δ)]
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    show load (a₀ ++ γ.drop a₀.length) δ = load γ δ
    rw [append_drop_of_prefix hγ.2]
  rw [h1]
  have h2 : nodeAgg T (fun γ => load γ δ) a₀
      = ∑ γ ∈ (treeLeaves T).filter (fun γ => a₀ <+: γ), load γ δ := by
    unfold nodeAgg
    rw [Finset.sum_filter]
  rw [h2]

/-- Take of an appended list past the prefix length. -/
theorem take_append_add {α : Type} {a₀ s : List α} (j : ℕ) :
    (a₀ ++ s).take (a₀.length + j) = a₀ ++ s.take j := by
  rw [List.take_append]
  simp

/-- Computing `treeLCA` from a maximal admissible index. -/
theorem treeLCA_take {α : Type} [DecidableEq α] {γ γ' : List α} {k : ℕ} (hk : k ≤ γ.length)
    (hmem : γ.take k <+: γ')
    (hmax : ∀ j, j ≤ γ.length → γ.take j <+: γ' → j ≤ k) :
    treeLCA γ γ' = γ.take k := by
  have hS : ((Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ')).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    exact List.nil_prefix
  have hmax' : ((Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ')).max' hS = k := by
    apply le_antisymm
    · apply Finset.max'_le
      intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      exact hmax j (by omega) hj.2
    · apply Finset.le_max'
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hmem⟩
  unfold treeLCA
  rw [hmax']

/-- LCA correspondence for re-rooting: the least common ancestor
relative to `a₀` is the drop of the absolute one. -/
theorem reroot_treeLCA {α : Type} [DecidableEq α] (a₀ s s' : List α) :
    treeLCA (a₀ ++ s) (a₀ ++ s') = a₀ ++ treeLCA s s' := by
  have hS : ((Finset.range (s.length + 1)).filter
      (fun j => s.take j <+: s')).Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    exact List.nil_prefix
  have hjmem' : ((Finset.range (s.length + 1)).filter
      (fun j => s.take j <+: s')).max' hS
      ∈ (Finset.range (s.length + 1)).filter (fun j => s.take j <+: s') :=
    Finset.max'_mem _ _
  have hjmem : s.take (((Finset.range (s.length + 1)).filter
      (fun j => s.take j <+: s')).max' hS) <+: s' :=
    (Finset.mem_filter.mp hjmem').2
  have hjle : ((Finset.range (s.length + 1)).filter
      (fun j => s.take j <+: s')).max' hS ≤ s.length := by
    have h1 := (Finset.mem_filter.mp hjmem').1
    rw [Finset.mem_range] at h1
    omega
  have hLCA : treeLCA s s'
      = s.take (((Finset.range (s.length + 1)).filter
        (fun j => s.take j <+: s')).max' hS) :=
    treeLCA_take hjle hjmem (fun j hj hmem => by
      apply Finset.le_max'
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hmem⟩)
  have htake : (a₀ ++ s).take
      (a₀.length + ((Finset.range (s.length + 1)).filter
        (fun j => s.take j <+: s')).max' hS)
      = a₀ ++ s.take (((Finset.range (s.length + 1)).filter
        (fun j => s.take j <+: s')).max' hS) :=
    take_append_add _
  have hmem : (a₀ ++ s).take
      (a₀.length + ((Finset.range (s.length + 1)).filter
        (fun j => s.take j <+: s')).max' hS) <+: a₀ ++ s' := by
    rw [htake]
    exact append_prefix_append_iff.mpr hjmem
  have hmax : ∀ i, i ≤ (a₀ ++ s).length →
      (a₀ ++ s).take i <+: a₀ ++ s' →
      i ≤ a₀.length + ((Finset.range (s.length + 1)).filter
        (fun j => s.take j <+: s')).max' hS := by
    intro i hi hpre
    by_cases hi0 : i ≤ a₀.length
    · omega
    · have hje : i - a₀.length ≤ s.length := by
        rw [List.length_append] at hi
        omega
      have htakei : (a₀ ++ s).take i
          = a₀ ++ s.take (i - a₀.length) := by
        have hie : i = a₀.length + (i - a₀.length) := by omega
        conv_lhs => rw [hie]
        exact take_append_add _
      have hjpre : s.take (i - a₀.length) <+: s' := by
        rw [htakei] at hpre
        exact append_prefix_append_iff.mp hpre
      have hle : i - a₀.length ≤ ((Finset.range (s.length + 1)).filter
          (fun j => s.take j <+: s')).max' hS := by
        apply Finset.le_max'
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hjpre⟩
      omega
  have hmain : treeLCA (a₀ ++ s) (a₀ ++ s')
      = (a₀ ++ s).take (a₀.length + ((Finset.range (s.length + 1)).filter
        (fun j => s.take j <+: s')).max' hS) :=
    treeLCA_take (by rw [List.length_append]; omega) hmem hmax
  rw [hmain, htake, hLCA]

/-- Pointwise domination implies subpower domination (nonnegative RHS). -/
theorem SubpowerLE.of_pointwise_le {x B : ℝ → ℝ}
    (hle : ∀ δ : ℝ, 0 < δ → δ < 1 → x δ ≤ B δ)
    (hB : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ B δ) :
    SubpowerLE x B := by
  intro ε hε
  refine ⟨1, zero_le_one, fun δ hδ0 hδ1 => ?_⟩
  have h1 : (1 : ℝ) ≤ δ ^ (-ε) := by
    rw [Real.rpow_neg (le_of_lt hδ0)]
    exact (one_le_inv_iff₀).mpr ⟨Real.rpow_pos_of_pos hδ0 ε,
      le_of_lt (Real.rpow_lt_one (le_of_lt hδ0) hδ1 hε)⟩
  calc x δ ≤ B δ := hle δ hδ0 hδ1
    _ = 1 * B δ := by ring
    _ ≤ δ ^ (-ε) * B δ :=
        mul_le_mul_of_nonneg_right h1 (hB δ hδ0 hδ1)
    _ = 1 * δ ^ (-ε) * B δ := by ring

/-- Division lemma: `x² ≲ B·x` implies `x ≲ B` for nonnegative `x`, `B`.
Paper §10: dividing the descent-step output `N(δ)² ≲ B^pred(δ)·N(δ)`
by `N(δ)` to obtain the invariant at the current vertex. -/
theorem SubpowerLE.div_of_sq {x B : ℝ → ℝ}
    (hx : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ x δ)
    (hB : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ B δ)
    (h : SubpowerLE (fun δ => (x δ) ^ 2) (fun δ => B δ * x δ)) :
    SubpowerLE x B := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
  have hbd := hb δ hδ0 hδ1
  by_cases hx0 : x δ = 0
  · rw [hx0]
    exact mul_nonneg (mul_nonneg hC
      (le_of_lt (Real.rpow_pos_of_pos hδ0 _))) (hB δ hδ0 hδ1)
  · have hxpos : 0 < x δ := lt_of_le_of_ne (hx δ hδ0 hδ1) (Ne.symm hx0)
    have h2 : x δ * x δ ≤ (C * δ ^ (-ε) * B δ) * x δ := by
      have h3 := hbd
      simp only [pow_two] at h3
      have h4 : C * δ ^ (-ε) * (B δ * x δ)
          = (C * δ ^ (-ε) * B δ) * x δ := by ring
      rw [h4] at h3
      exact h3
    exact le_of_mul_le_mul_right h2 hxpos

end FilteredDescent
