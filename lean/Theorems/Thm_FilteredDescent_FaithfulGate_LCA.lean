import Definitions.Def_FilteredDescent_Tree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

/-!
# Faithful root-cross gate — LCA/children infrastructure (paper §10)

General facts about `treeLCA` (longest common prefix) and root children
in a prefix-closed history tree, needed for the faithful formalization of
the paper's root-cross gate:

* `treeLCA_eq_of_take_ne` / `treeLCA_ne_of_take_eq`: for words `γ, γ'`
  under a common prefix `a`, the LCA is exactly `a` iff the
  length-`a.length+1` prefixes differ.  This is the combinatorial heart
  of (140)/(146): root-cross pairs are exactly pairs of leaves under
  distinct root children.
* `treeLCA_eq_root_iff`: the root case, for non-root leaves.
* `leaf_take1_mem_children` / `take1_eq_of_child_mem`: every non-root
  leaf lies under a root child.

All statements are for general prefix-closed trees — no toy instances.
-/

namespace FilteredDescent

/-- The LCA prefixes the first word. -/
theorem treeLCA_prefix_left {α : Type} [DecidableEq α] (γ γ' : List α) :
    treeLCA γ γ' <+: γ := by
  unfold treeLCA
  exact List.take_prefix _ γ

/-- The LCA prefixes the second word. -/
theorem treeLCA_prefix_right {α : Type} [DecidableEq α] (γ γ' : List α) :
    treeLCA γ γ' <+: γ' := by
  unfold treeLCA
  have hmem := Finset.max'_mem _
    (⟨0, by simp⟩ : ((Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ')).Nonempty)
  rw [Finset.mem_filter] at hmem
  exact hmem.2

/-- The LCA of two tree nodes lies in a prefix-closed tree. -/
theorem treeLCA_mem_tree {α : Type} [DecidableEq α] {T : Finset (List α)}
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    {γ γ' : List α} (hγ : γ ∈ T) (_hγ' : γ' ∈ T) :
    treeLCA γ γ' ∈ T :=
  hprefix γ hγ _ (treeLCA_prefix_left γ γ')

/-- If `LCA(γ,γ') = a` then `a` prefixes both words. -/
theorem treeLCA_eq_imp_prefix {α : Type} [DecidableEq α]
    {a γ γ' : List α} (h : treeLCA γ γ' = a) :
    a <+: γ ∧ a <+: γ' := by
  rw [← h]
  exact ⟨treeLCA_prefix_left γ γ', treeLCA_prefix_right γ γ'⟩

/-- A take-prefix of a take-prefix is a prefix. -/
private theorem take_prefix_take {α : Type} (l : List α) {n m : ℕ}
    (h : n ≤ m) : l.take n <+: l.take m := by
  have heq : l.take n = (l.take m).take n := by
    rw [List.take_take]
    congr 1
    omega
  rw [heq]
  exact List.take_prefix n (l.take m)

/-- The definitional unfolding of `treeLCA`, with the `Nonempty` proof
abstracted (proof irrelevance makes the choice immaterial). -/
private theorem treeLCA_unfold {α : Type} [DecidableEq α] (γ γ' : List α)
    (H : ((Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ')).Nonempty) :
    treeLCA γ γ' = γ.take (((Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ')).max' H) := rfl

/-- LCA computation: if `a` prefixes both words but the
length-`a.length+1` takes differ, the LCA is exactly `a`. -/
theorem treeLCA_eq_of_take_ne {α : Type} [DecidableEq α]
    {a γ γ' : List α} (haγ : a <+: γ) (haγ' : a <+: γ')
    (hne : γ.take (a.length + 1) ≠ γ'.take (a.length + 1)) :
    treeLCA γ γ' = a := by
  have ha_mem : a.length ∈ (Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ') := by
    rw [Finset.mem_filter, Finset.mem_range]
    have h1 : γ.take a.length = a := (List.prefix_iff_eq_take.mp haγ).symm
    refine ⟨Nat.lt_succ_of_le (List.IsPrefix.length_le haγ), ?_⟩
    rw [h1]
    exact haγ'
  have hle : ∀ k ∈ (Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ'), k ≤ a.length := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    by_contra hcon
    push Not at hcon
    -- `hcon : a.length < k`: then `γ.take (a.length+1)` prefixes `γ'`,
    -- forcing the two takes to be equal.
    have hkle : k ≤ γ.length := Nat.le_of_lt_succ hk.1
    have hpre : γ.take (a.length + 1) <+: γ' :=
      (take_prefix_take γ (by omega)).trans hk.2
    have hlen : (γ.take (a.length + 1)).length = a.length + 1 := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    have heq : γ.take (a.length + 1) = γ'.take (a.length + 1) := by
      have h2 := List.prefix_iff_eq_take.mp hpre
      rw [hlen] at h2
      exact h2
    exact hne heq
  have hmax : ((Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ')).max' ⟨a.length, ha_mem⟩ = a.length :=
    le_antisymm (Finset.max'_le _ _ _ hle) (Finset.le_max' _ _ ha_mem)
  rw [treeLCA_unfold γ γ' ⟨a.length, ha_mem⟩, hmax]
  exact (List.prefix_iff_eq_take.mp haγ).symm

/-- LCA computation, converse direction: if the length-`a.length+1` takes
agree and are full-length, the LCA is strictly longer than `a`. -/
theorem treeLCA_ne_of_take_eq {α : Type} [DecidableEq α]
    {a γ γ' : List α} (_haγ : a <+: γ) (_haγ' : a <+: γ')
    (heq : γ.take (a.length + 1) = γ'.take (a.length + 1))
    (hfull : (γ.take (a.length + 1)).length = a.length + 1) :
    treeLCA γ γ' ≠ a := by
  have hle1 : a.length + 1 ≤ γ.length := by
    rw [List.length_take] at hfull
    omega
  have hmem : a.length + 1 ∈ (Finset.range (γ.length + 1)).filter
      (fun k => γ.take k <+: γ') := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le hle1, ?_⟩
    rw [heq]
    exact List.take_prefix _ γ'
  intro hcon
  have hlen : a.length + 1 ≤ (treeLCA γ γ').length := by
    rw [treeLCA_unfold γ γ' ⟨a.length + 1, hmem⟩, List.length_take]
    have hge : a.length + 1 ≤ ((Finset.range (γ.length + 1)).filter
        (fun k => γ.take k <+: γ')).max' ⟨a.length + 1, hmem⟩ :=
      Finset.le_max' _ _ hmem
    have hk_le : ((Finset.range (γ.length + 1)).filter
        (fun k => γ.take k <+: γ')).max' ⟨a.length + 1, hmem⟩ ≤ γ.length := by
      have hmm := Finset.max'_mem _ ⟨a.length + 1, hmem⟩
      rw [Finset.mem_filter, Finset.mem_range] at hmm
      exact Nat.le_of_lt_succ hmm.1
    omega
  rw [hcon] at hlen
  omega

/-- A non-root word has a full-length take-1. -/
private theorem take_one_full {α : Type} {γ : List α} (hne : γ ≠ []) :
    (γ.take 1).length = 1 := by
  rw [List.length_take]
  have h1 : 1 ≤ γ.length := by
    rcases Nat.eq_zero_or_pos γ.length with h0 | hpos
    · exfalso; exact hne (List.eq_nil_of_length_eq_zero h0)
    · exact hpos
  exact Nat.min_eq_left h1

/-- Root case: for a non-root first word, `LCA = []` iff the length-1 takes differ. -/
theorem treeLCA_eq_root_iff {α : Type} [DecidableEq α]
    {γ γ' : List α} (hne1 : γ ≠ []) :
    (treeLCA γ γ' = [] ↔ γ.take 1 ≠ γ'.take 1) := by
  constructor
  · intro h contra
    have hfull : (γ.take (([] : List α).length + 1)).length
        = ([] : List α).length + 1 := by
      simpa using take_one_full hne1
    have h2 := treeLCA_ne_of_take_eq (a := ([] : List α))
      List.nil_prefix List.nil_prefix (by simpa using contra) hfull
    exact h2 h
  · intro h
    have h1 := treeLCA_eq_of_take_ne (a := ([] : List α)) (γ := γ) (γ' := γ')
      (List.nil_prefix (l := γ)) (List.nil_prefix (l := γ'))
    have hne : γ.take (([] : List α).length + 1)
        ≠ γ'.take (([] : List α).length + 1) := by
      simpa using h
    exact h1 hne

/-- Every non-root leaf lies under a root child. -/
theorem leaf_take1_mem_children {α : Type} [DecidableEq α] {T : Finset (List α)}
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    {γ : List α} (hγ : γ ∈ treeLeaves T) (hne : γ ≠ []) :
    γ.take 1 ∈ treeChildren T [] ∧ γ.take 1 <+: γ := by
  have hmem : γ ∈ T := Finset.mem_of_mem_filter γ hγ
  have hpre : γ.take 1 <+: γ := List.take_prefix 1 γ
  have hlen : (γ.take 1).length = 1 := take_one_full hne
  refine ⟨?_, hpre⟩
  rw [treeChildren, Finset.mem_filter]
  refine ⟨hprefix γ hmem _ hpre, List.nil_prefix, ?_⟩
  simpa using hlen

/-- A leaf under a root child has that child as its length-1 take. -/
theorem take1_eq_of_child_mem {α : Type} [DecidableEq α] {T : Finset (List α)}
    {b : List α} (hb : b ∈ treeChildren T [])
    {γ : List α} (hble : b <+: γ) : γ.take 1 = b := by
  rw [treeChildren, Finset.mem_filter] at hb
  obtain ⟨-, -, hb2⟩ := hb
  have h1 : b = γ.take b.length := List.prefix_iff_eq_take.mp hble
  have h2 : b.length = 1 := by simpa using hb2
  rw [h2] at h1
  exact h1.symm

end FilteredDescent
