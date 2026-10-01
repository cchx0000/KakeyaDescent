import Definitions.Def_FilteredDescent_Tree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# M6b — R5 insufficiency model (paper §10.5)

The paper's one-point model showing chartwise R5 does not imply the
duplicate bound: `R` leaf histories, each of unit mass, all ending in the
same terminal tube.  Chartwise R5 holds with `B = 1` (every single history
has mass `≤ 1`), `∫N = R`, but `X^{root} = R^2 - R`, so
`X^{root} / (B · ∫N) = R - 1` is unbounded in `R` — no `R`-independent
bound `X^{root} ≤ C · B · ∫N` can hold.
-/

namespace FilteredDescent

theorem r5_insufficiency_model (R : ℕ) (hR : 2 ≤ R) :
    let T : Finset (List ℕ) := {[]} ∪ (Finset.range R).image (fun k => [k]);
    let u : List ℕ → ℝ :=
      fun γ => if γ ∈ (Finset.range R).image (fun k => [k]) then 1 else 0;
    Xroot T u = (R : ℝ) ^ 2 - R ∧
      (∑ γ ∈ treeLeaves T, u γ) = (R : ℝ) ∧
      ∀ γ ∈ treeLeaves T, u γ ≤ 1 := by
  intro T u
  have hT : T = {[]} ∪ (Finset.range R).image (fun k => [k]) := rfl
  have hu : u = fun γ => if γ ∈ (Finset.range R).image (fun k => [k]) then (1:ℝ) else 0 := rfl
  -- The singleton map is injective on `range R`.
  have himg_inj : Set.InjOn (fun k => [k]) ((Finset.range R : Finset ℕ) : Set ℕ) := by
    intro x _ y _ h
    simp only at h
    cases h
    rfl
  -- A singleton prefix determines the element.
  have hsing_pre : ∀ k k' : ℕ, [k] <+: [k'] → k = k' := by
    intro k k' h
    obtain ⟨t, ht⟩ := h
    have hlen2 : t.length = 0 := by
      have h2 := congrArg List.length ht
      simp only [List.length_singleton, List.length_append] at h2
      omega
    have ht0 : t = [] := List.eq_nil_of_length_eq_zero hlen2
    rw [ht0, List.append_nil] at ht
    cases ht
    rfl
  -- A singleton is never `[]`.
  have hne_single : ∀ k : ℕ, ([k] : List ℕ) ≠ [] := fun k h => by cases h
  -- Leaves are exactly the singletons `[k]`, `k < R`.
  have hleaves : treeLeaves T = (Finset.range R).image (fun k => [k]) := by
    rw [hT]
    ext l
    simp only [treeLeaves, Finset.mem_filter]
    constructor
    · rintro ⟨hmem, hmax⟩
      rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hmem
      rcases hmem with rfl | ⟨k, hk, rfl⟩
      · exfalso
        have h0mem : ([0] : List ℕ) ∈ ({[]} : Finset (List ℕ)) ∪ (Finset.range R).image (fun k => [k]) := by
          apply Finset.mem_union.mpr
          right
          apply Finset.mem_image.mpr
          exact ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
        have h01 : ([0] : List ℕ) = [] := hmax [0] h0mem List.nil_prefix
        exact (by decide : ([0] : List ℕ) ≠ []) h01
      · exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨k, hk, rfl⟩ := hmem
      refine ⟨?_, ?_⟩
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        exact ⟨k, hk, rfl⟩
      · intro l' hl' hpre
        rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hl'
        rcases hl' with rfl | ⟨k', hk', hkk'⟩
        · exfalso
          have hcon : ([k] : List ℕ) = [] := List.prefix_nil.mp hpre
          exact (hne_single k) hcon
        · rw [← hkk'] at hpre
          have heq : k = k' := hsing_pre k k' hpre
          rw [← hkk', heq]
  -- LCA of `[k]` with itself is `[k]`.
  have hLCA_eq : ∀ k : ℕ, treeLCA [k] [k] = [k] := by
    intro k
    have hlen : ([k] : List ℕ).length = 1 := rfl
    have h1mem : 1 ∈ (Finset.range ([k].length + 1)).filter (fun k_ => [k].take k_ <+: [k]) := by
      rw [Finset.mem_filter, Finset.mem_range, hlen]
      refine ⟨by decide, ?_⟩
      show ([k] : List ℕ) <+: [k]
      exact List.prefix_rfl
    have hle1 : ∀ x ∈ (Finset.range ([k].length + 1)).filter (fun k_ => [k].take k_ <+: [k]), x ≤ 1 := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_range, hlen] at hx
      omega
    have hmax : ((Finset.range ([k].length + 1)).filter (fun k_ => [k].take k_ <+: [k])).max' ⟨1, h1mem⟩ = 1 :=
      le_antisymm (Finset.max'_le _ _ 1 hle1) (Finset.le_max' _ _ h1mem)
    have htake : List.take 1 [k] = [k] := rfl
    unfold treeLCA
    rw [hmax, htake]
  -- LCA of distinct singletons is `[]`.
  have hLCA_ne : ∀ k k' : ℕ, k ≠ k' → treeLCA [k] [k'] = [] := by
    intro k k' hne
    have hlen : ([k] : List ℕ).length = 1 := rfl
    have hSeq : (Finset.range ([k].length + 1)).filter (fun k_ => [k].take k_ <+: [k']) = {0} := by
      ext x
      rw [Finset.mem_filter, Finset.mem_range, hlen, Finset.mem_singleton]
      constructor
      · rintro ⟨hx2, hpre⟩
        by_contra hx0
        have hx1 : x = 1 := by omega
        subst hx1
        have hpre' : ([k] : List ℕ) <+: [k'] := by simpa using hpre
        exact hne (hsing_pre k k' hpre')
      · intro hx
        subst hx
        refine ⟨by decide, ?_⟩
        show ([k] : List ℕ).take 0 <+: [k']
        rw [List.take_zero]
        exact List.nil_prefix
    have h0mem : 0 ∈ (Finset.range ([k].length + 1)).filter (fun k_ => [k].take k_ <+: [k']) := by
      rw [Finset.mem_filter, Finset.mem_range, hlen]
      refine ⟨by decide, ?_⟩
      show ([] : List ℕ) <+: [k']
      exact List.nil_prefix
    have hmax0 : ((Finset.range ([k].length + 1)).filter (fun k_ => [k].take k_ <+: [k'])).max' ⟨0, h0mem⟩ = 0 := by
      apply le_antisymm _ (Nat.zero_le _)
      apply Finset.max'_le _ _ 0
      intro x hx
      rw [hSeq, Finset.mem_singleton] at hx
      omega
    unfold treeLCA
    rw [hmax0, List.take_zero]
  have hLCA : ∀ k k' : ℕ, treeLCA [k] [k'] = [] ↔ k ≠ k' := by
    intro k k'
    constructor
    · intro hcon hkk
      subst hkk
      rw [hLCA_eq k] at hcon
      exact (hne_single k) hcon
    · exact hLCA_ne k k'
  -- `u` is 1 on singletons.
  have hu1 : ∀ k ∈ Finset.range R, u [k] = 1 := by
    intro k hk
    have hmem : [k] ∈ (Finset.range R).image (fun k => [k]) :=
      Finset.mem_image.mpr ⟨k, hk, rfl⟩
    rw [hu]
    show (if [k] ∈ (Finset.range R).image (fun k => [k]) then (1:ℝ) else 0) = 1
    exact if_pos hmem
  -- Part 1: `Xroot = R^2 - R`.
  have hX : Xroot T u = (R:ℝ)^2 - R := by
    have e1 : Xroot T u = ∑ k ∈ Finset.range R, ∑ k' ∈ Finset.range R,
        (if k ≠ k' then (1:ℝ) else 0) := by
      unfold Xroot
      rw [hleaves, Finset.sum_image himg_inj]
      show (∑ k ∈ Finset.range R, ∑ γ' ∈ (Finset.range R).image (fun k => [k]),
        (if treeLCA [k] γ' = [] then u [k] * u γ' else 0)) = _
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.sum_image himg_inj]
      show (∑ k' ∈ Finset.range R,
        (if treeLCA [k] [k'] = [] then u [k] * u [k'] else 0)) = _
      refine Finset.sum_congr rfl fun k' hk' => ?_
      by_cases hkk : k ≠ k'
      · have hcond : treeLCA [k] [k'] = [] := (hLCA k k').mpr hkk
        rw [if_pos hcond, if_pos hkk, hu1 k hk, hu1 k' hk', mul_one]
      · have hcond : ¬ treeLCA [k] [k'] = [] := fun h => hkk ((hLCA k k').mp h)
        rw [if_neg hcond, if_neg hkk]
    have e2 : ∀ k ∈ Finset.range R,
        (∑ k' ∈ Finset.range R, (if k ≠ k' then (1:ℝ) else 0)) = (R:ℝ) - 1 := by
      intro k hk
      have hfilter : (Finset.range R).filter (fun k' => k ≠ k') = (Finset.range R).erase k := by
        ext k'
        rw [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨Ne.symm h2, h1⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h2, Ne.symm h1⟩
      have hcard : ((Finset.range R).filter (fun k' => k ≠ k')).card = R - 1 := by
        rw [hfilter, Finset.card_erase_of_mem hk, Finset.card_range]
      calc ∑ k' ∈ Finset.range R, (if k ≠ k' then (1:ℝ) else 0)
          = ∑ k' ∈ (Finset.range R).filter (fun k' => k ≠ k'), (1:ℝ) := by
            rw [← Finset.sum_filter]
        _ = (((Finset.range R).filter (fun k' => k ≠ k')).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ = (R:ℝ) - 1 := by
            rw [hcard, Nat.cast_sub (by omega : 1 ≤ R), Nat.cast_one]
    rw [e1]
    calc ∑ k ∈ Finset.range R, ∑ k' ∈ Finset.range R, (if k ≠ k' then (1:ℝ) else 0)
        = ∑ k ∈ Finset.range R, ((R:ℝ) - 1) := Finset.sum_congr rfl (fun k hk => e2 k hk)
      _ = (R:ℝ)^2 - R := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- Part 2: the mass sum is `R`.
  have hSum : (∑ γ ∈ treeLeaves T, u γ) = (R:ℝ) := by
    calc ∑ γ ∈ treeLeaves T, u γ
        = ∑ k ∈ Finset.range R, u [k] := by rw [hleaves, Finset.sum_image himg_inj]
      _ = ∑ k ∈ Finset.range R, (1:ℝ) := Finset.sum_congr rfl (fun k hk => hu1 k hk)
      _ = (R:ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  -- Part 3: `u ≤ 1` on leaves.
  have hle1 : ∀ γ ∈ treeLeaves T, u γ ≤ 1 := by
    intro γ _
    rw [hu]
    show (if γ ∈ (Finset.range R).image (fun k => [k]) then (1:ℝ) else 0) ≤ 1
    by_cases h : γ ∈ (Finset.range R).image (fun k => [k])
    · rw [if_pos h]
    · rw [if_neg h]; exact zero_le_one
  exact ⟨hX, hSum, hle1⟩

end FilteredDescent
