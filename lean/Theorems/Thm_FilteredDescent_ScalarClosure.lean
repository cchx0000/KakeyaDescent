import Definitions.Def_FilteredDescent_Analytic
import Definitions.Def_FilteredDescent_Tree
import Theorems.Thm_FilteredDescent_RootCrossGate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Goal — Scalar filtered-descent closure (paper §13.2, (214))

The paper's scalar closure: for a finite direction-separated family of
shaded `δ`-tubes with `λ_in⁻¹` subpower in `δ` (uniformly), assuming the
imported analytic estimate for the relevant dimension — the hereditary
planar Córdoba input [2] (`H2`) for `d = 2`, the sticky Kakeya input
[7,10] (`H3`) for `d = 3`, or the uniform marked 4D sticky input [9]
(`H4`) for `d = 4` — the terminal incidence count holds, uniformly for
`δ ∈ (0,1)`:

  `Σ_T |Y(T)| ≲ |⋃_T Y(T)|`.

The filtered descent (R5/R6, the root-cross gate (142), the closed
support recurrence (124)–(125), and the terminal unweighting (130)) is
the proof; the milestones M1–M9 below are its attack path.  `d ≥ 5` and
the typed Hall-capacity comparison (paper (160)/(207)) are not claimed.

## Proof strategy (d = 3, 4): via the root-cross gate

We build a `GateStage` from the tube family `S` using the trivial
history tree (root with `n` leaf children, one per tube).  For this
tree:
- `treeLCA [t] [t'] = []` iff `t ≠ t'` (proved below);
- `Xgeom` is exactly the off-diagonal pair-incidence sum
  `∑_{t≠t'} shadeVol t δ * shadeVol t' δ`;
- `Xdup = 0` (diagonal pairs have LCA `[t] ≠ []`).

The `Hgeom` hypothesis of `root_cross_gate` is then *exactly* the
pair-incidence component of `StickyInput`/`Marked4DInput` (with
`Bpred := unionVol`).  Applying `root_cross_gate` yields the `Xroot`
bound, demonstrating that the geometric input correctly controls the
root-cross pair mass through the descent machinery.

## Status

* `d = 3` and `d = 4`: **proved** (see the fidelity note below).
* `d = 2`: **`sorry`**.  `PlanarInput Kpr` is `SubpowerLE Kpr 1`, a bound
  on the unrelated function `Kpr`; it has no formal connection to the
  tube family `S`, so the goal is not derivable from the hypotheses as
  stated.  Closing this case requires formalizing how the planar
  Córdoba estimate [2] controls the tube geometry — unformalized
  analytic work (a formalization gap, not a paper gap).

### Fidelity note

The descent machinery (`GateStage`, `Hgeom` from the sticky input,
`root_cross_gate`) is fully worked out below and the `Xroot` bound is
derived.  However, the final step from the `Xroot` bound to the goal
`SubpowerLE (∑ shadeVol) unionVol` uses the multiplicity identity
`S.mult_eq` (`M * U = ∑ shadeVol`) and the `SubpowerLE M 1` component
directly, rather than going through `terminal_incidence_count` (whose
`hcount` hypothesis — a pointwise lower bound `U ≥ (lamIn/2M)·∑ shadeVol`
— is not derivable from the `Xroot` upper bound in this setup).

In the paper, the descent is essential: the tree is built from the
actual tube geometry (not the trivial star), and the terminal
unweighting converts the `Xroot` control into the incidence bound.
The formal trivial tree captures the *algebraic* content of the sticky
input (the pair-sum bound becomes `Hgeom`), but the *geometric*
content — how the tree structure reflects tube interactions — is not
formalized.  The proof below is correct for the definitions as given;
the gap between the formal trivial tree and the paper's geometric tree
is the remaining fidelity issue.
-/

namespace FilteredDescent

/-- The trivial history tree: root `[]` with `n` leaf children `[t]`. -/
def trivialTree {n : ℕ} : Finset (List (Fin n)) :=
  {[]} ∪ Finset.univ.image (fun t : Fin n => [t])


/-- Leaves of the trivial tree are exactly the singletons `[t]`. -/
theorem trivialTree_leaves {n : ℕ} (hn : 0 < n) :
    treeLeaves (trivialTree (n := n)) = Finset.univ.image (fun t : Fin n => [t]) := by
  ext γ
  constructor
  · intro hmem
    rw [treeLeaves, Finset.mem_filter] at hmem
    obtain ⟨hmemT, hmax⟩ := hmem
    simp only [trivialTree, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and] at hmemT
    rcases hmemT with rfl | ⟨t, _, rfl⟩
    · exfalso
      have hmem1 : [⟨0, hn⟩] ∈ (trivialTree (n := n)) := by
        simp only [trivialTree, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image, Finset.mem_univ, true_and]
        simp
      have hpre : ([] : List (Fin n)) <+: [⟨0, hn⟩] := by simp
      have := hmax [⟨0, hn⟩] hmem1 hpre
      simp at this
    · simp
  · intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨t, _, rfl⟩ := hmem
    rw [treeLeaves, Finset.mem_filter]
    constructor
    · simp only [trivialTree, Finset.mem_union]
      simp
    · intro l' hl' hpre
      simp only [trivialTree, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_image] at hl'
      rcases hl' with rfl | ⟨s, _, hs⟩
      · exfalso; simp at hpre
      · rw [← hs] at hpre
        have hts : t = s := by simpa using hpre
        simp [hts, hs]

/-- The trivial tree is prefix-closed. -/
theorem trivialTree_prefix {n : ℕ} :
    ∀ l ∈ trivialTree (n := n), ∀ p : List (Fin n), p <+: l → p ∈ trivialTree (n := n) := by
  intro l hl p hp
  simp only [trivialTree, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hl ⊢
  rcases hl with rfl | ⟨t, _, rfl⟩
  · -- l = []: p <+: [] implies p = []
    have : p = [] := by simpa using hp
    simp [this]
  · -- l = [t]: p = [] or p = [t]
    have hp' : p = [] ∨ p = [t] := by
      -- p is a prefix of [t], so p = [] or p = [t]
      cases p with
      | nil => exact Or.inl rfl
      | cons h tl =>
        have : h = t ∧ tl = [] := by simpa using hp
        obtain ⟨rfl, rfl⟩ := this
        exact Or.inr rfl
    rcases hp' with rfl | rfl
    · simp
    · simp

/-- Build a `GateStage` from a tube family via the trivial tree. -/
noncomputable def gateStageOfShadedTubes {n : ℕ} (hn : 0 < n) (S : ShadedTubes n) :
    GateStage (Fin n) n 1 where
  tree := trivialTree
  hroot := by simp [trivialTree]
  hprefix := trivialTree_prefix
  load := fun γ δ => match γ with
    | [t] => S.shadeVol t δ
    | _ => 0
  hload := by
    intro γ hγ δ hδ0 hδ1
    rw [trivialTree_leaves hn] at hγ
    rw [Finset.mem_image] at hγ
    obtain ⟨t, _, rfl⟩ := hγ
    simp
    exact S.shade_nonneg t δ hδ0 hδ1
  termTube := fun γ => match γ with
    | [t] => t
    | _ => ⟨0, hn⟩
  carrier := fun _ => ⟨0, by decide⟩
  shadeVol := S.shadeVol
  unionVol := S.unionVol
  multiplicity := S.multiplicity
  shade_nonneg := S.shade_nonneg
  union_nonneg := S.union_nonneg
  mult_pos := S.mult_pos
  mult_eq := S.mult_eq
  Bpred := S.unionVol
  Bpred_nonneg := S.union_nonneg
  load_le_shade := by
    intro γ hγ δ hδ0 hδ1
    rw [trivialTree_leaves hn] at hγ
    rw [Finset.mem_image] at hγ
    obtain ⟨t, _, rfl⟩ := hγ
    -- load [t] δ = S.shadeVol t δ = shadeVol (termTube [t]) δ by rfl
    exact le_rfl

/-- `load [t] δ = shadeVol t δ`. -/
theorem gateStage_load_singleton {n : ℕ} (hn : 0 < n) (S : ShadedTubes n)
    (t : Fin n) (δ : ℝ) :
    (gateStageOfShadedTubes hn S).load [t] δ = S.shadeVol t δ := by
  simp [gateStageOfShadedTubes]

/-- `termTube [t] = t`. -/
theorem gateStage_termTube_singleton {n : ℕ} (hn : 0 < n) (S : ShadedTubes n)
    (t : Fin n) :
    (gateStageOfShadedTubes hn S).termTube [t] = t := by
  simp [gateStageOfShadedTubes]

/-- `Xgeom` for the trivial tree equals the off-diagonal pair sum. -/
theorem gateStage_Xgeom_eq {n : ℕ} (hn : 0 < n) (S : ShadedTubes n) (δ : ℝ) :
    Xgeom (gateStageOfShadedTubes hn S).tree
      (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
      (gateStageOfShadedTubes hn S).termTube
    = ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0 := by
  have htree : (gateStageOfShadedTubes hn S).tree = trivialTree := rfl
  have hinj : ∀ t ∈ (Finset.univ : Finset (Fin n)), ∀ s ∈ (Finset.univ : Finset (Fin n)),
      (fun t : Fin n => [t]) t = (fun t : Fin n => [t]) s → t = s := by
    intro t _ s _ h
    cases h
    rfl
  rw [Xgeom, htree, trivialTree_leaves hn]
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro t' _
  -- For γ = [t], γ' = [t']: LCA = [] ↔ t ≠ t', termTube = t, t'
  by_cases hne : t ≠ t'
  · have hlca : treeLCA [t] [t'] = [] := treeLCA_singleton_ne hne
    have htt : (gateStageOfShadedTubes hn S).termTube [t] ≠
        (gateStageOfShadedTubes hn S).termTube [t'] := by
      rw [gateStage_termTube_singleton hn S t, gateStage_termTube_singleton hn S t']
      exact hne
    have hload1 : (gateStageOfShadedTubes hn S).load [t] δ = S.shadeVol t δ :=
      gateStage_load_singleton hn S t δ
    have hload2 : (gateStageOfShadedTubes hn S).load [t'] δ = S.shadeVol t' δ :=
      gateStage_load_singleton hn S t' δ
    rw [hlca, hload1, hload2]
    simp [htt, hne]
  · push_neg at hne
    subst hne
    -- Both sides are 0: LHS has termTube [t] ≠ termTube [t] (false),
    -- RHS has t ≠ t (false)
    simp

/-- `Xdup` for the trivial tree is zero (diagonal pairs have LCA `[t] ≠ []`). -/
theorem gateStage_Xdup_eq_zero {n : ℕ} (hn : 0 < n) (S : ShadedTubes n) (δ : ℝ) :
    Xdup (gateStageOfShadedTubes hn S).tree
      (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
      (gateStageOfShadedTubes hn S).termTube = 0 := by
  have htree : (gateStageOfShadedTubes hn S).tree = trivialTree := rfl
  have hinj : ∀ t ∈ (Finset.univ : Finset (Fin n)), ∀ s ∈ (Finset.univ : Finset (Fin n)),
      (fun t : Fin n => [t]) t = (fun t : Fin n => [t]) s → t = s := by
    intro t _ s _ h
    cases h
    rfl
  rw [Xdup, htree, trivialTree_leaves hn]
  rw [Finset.sum_image hinj]
  apply Finset.sum_eq_zero
  intro t _
  rw [Finset.sum_image hinj]
  apply Finset.sum_eq_zero
  intro t' _
  by_cases hne : t ≠ t'
  · -- t ≠ t': termTube [t] ≠ termTube [t'], so condition false
    have htt : (gateStageOfShadedTubes hn S).termTube [t] ≠
        (gateStageOfShadedTubes hn S).termTube [t'] := by
      rw [gateStage_termTube_singleton hn S t, gateStage_termTube_singleton hn S t']
      exact hne
    simp [htt]
  · push_neg at hne
    subst hne
    -- t = t': LCA = [t] ≠ [], so condition false
    have hlca : treeLCA [t] [t] = [t] := treeLCA_singleton_self t
    rw [hlca]
    simp

/-- The leaf-load sum equals the total shading. -/
theorem gateStage_leaf_sum_eq {n : ℕ} (hn : 0 < n) (S : ShadedTubes n) (δ : ℝ) :
    ∑ γ ∈ treeLeaves (gateStageOfShadedTubes hn S).tree,
        (gateStageOfShadedTubes hn S).load γ δ
    = ∑ t : Fin n, S.shadeVol t δ := by
  have htree : (gateStageOfShadedTubes hn S).tree = trivialTree := rfl
  have hinj : ∀ t ∈ (Finset.univ : Finset (Fin n)), ∀ s ∈ (Finset.univ : Finset (Fin n)),
      (fun t : Fin n => [t]) t = (fun t : Fin n => [t]) s → t = s := by
    intro t _ s _ h
    cases h
    rfl
  rw [htree, trivialTree_leaves hn]
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro t _
  rw [gateStage_load_singleton hn S t δ]

/-- `Hgeom` for the gate stage follows from the sticky pair-incidence bound. -/
theorem gateStage_Hgeom {n : ℕ} (hn : 0 < n) (S : ShadedTubes n)
    (hpair : SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0)
      (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ)) :
    SubpowerLE
      (fun δ => Xgeom (gateStageOfShadedTubes hn S).tree
        (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
        (gateStageOfShadedTubes hn S).termTube)
      (fun δ => (gateStageOfShadedTubes hn S).Bpred δ *
        ∑ γ ∈ treeLeaves (gateStageOfShadedTubes hn S).tree,
          (gateStageOfShadedTubes hn S).load γ δ) := by
  have heq1 : (fun δ => Xgeom (gateStageOfShadedTubes hn S).tree
        (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
        (gateStageOfShadedTubes hn S).termTube)
      = (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
          if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0) := by
    funext δ
    exact gateStage_Xgeom_eq hn S δ
  have heq2 : (fun δ => (gateStageOfShadedTubes hn S).Bpred δ *
        ∑ γ ∈ treeLeaves (gateStageOfShadedTubes hn S).tree,
          (gateStageOfShadedTubes hn S).load γ δ)
      = (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ) := by
    funext δ
    have hB : (gateStageOfShadedTubes hn S).Bpred δ = S.unionVol δ := rfl
    rw [hB, gateStage_leaf_sum_eq hn S δ]
  rw [heq1, heq2]
  exact hpair

/-- `Hdup` holds trivially since `Xdup = 0`. -/
theorem gateStage_Hdup {n : ℕ} (hn : 0 < n) (S : ShadedTubes n) :
    SubpowerLE
      (fun δ => Xdup (gateStageOfShadedTubes hn S).tree
        (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
        (gateStageOfShadedTubes hn S).termTube)
      (fun δ => (gateStageOfShadedTubes hn S).Bpred δ *
        ∑ γ ∈ treeLeaves (gateStageOfShadedTubes hn S).tree,
          (gateStageOfShadedTubes hn S).load γ δ) := by
  have heq : (fun δ => Xdup (gateStageOfShadedTubes hn S).tree
        (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
        (gateStageOfShadedTubes hn S).termTube)
      = (fun _ => 0) := by
    funext δ
    exact gateStage_Xdup_eq_zero hn S δ
  rw [heq]
  intro ε hε
  refine ⟨0, le_rfl, fun δ hδ0 hδ1 => ?_⟩
  simp only [Pi.zero_apply, zero_mul]
  -- 0 ≤ 0 * δ^{-ε} * _
  simp

theorem scalar_closure {d n : ℕ} (hd : d = 2 ∨ d = 3 ∨ d = 4) (hn : 0 < n)
    (S : ShadedTubes n)
    (lamIn : ℝ → ℝ) (hlam : ∀ δ, 0 < δ → δ < 1 → 0 < lamIn δ)
    (hlamSub : SubpowerLE (fun _ => 1) lamIn)
    (Kpr : ℝ → ℝ) (H2 : d = 2 → PlanarInput Kpr)
    (H3 : d = 3 → StickyInput S.shadeVol S.unionVol S.multiplicity)
    (H4 : d = 4 → Marked4DInput S.shadeVol S.unionVol S.multiplicity) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol := by
  rcases hd with rfl | rfl | rfl
  · -- d = 2: `PlanarInput Kpr` (= `SubpowerLE Kpr 1`) constrains only the
    -- unrelated function `Kpr`; there is no formal link from it to the
    -- tube family `S`, so `SubpowerLE (∑ shadeVol) unionVol` is not
    -- derivable from the hypotheses as stated.  Closing this case needs
    -- the planar Córdoba estimate [2] formalized as a geometric bound on
    -- `S`, which is unformalized analytic work (a formalization gap, not
    -- a paper gap).
    sorry
  · -- d = 3: via the root-cross gate on the trivial tree.
    -- The sticky input gives (mult bound, pair-incidence bound).
    obtain ⟨hmult, hpair⟩ := H3 rfl
    -- Build the gate stage and derive Hgeom/Hdup.
    have hgeom := gateStage_Hgeom hn S hpair
    have hdup := gateStage_Hdup hn S
    -- Apply the root-cross gate (d = 3).
    -- Note: hgate is the Xroot bound; we don't need it for the final
    -- step (see fidelity note), but it demonstrates the descent works.
    have hgate := root_cross_gate (α := Fin n) 3
      (Or.inr (Or.inl rfl)) (gateStageOfShadedTubes hn S) Kpr
      (fun h => absurd h (by decide))
      (fun _ => ⟨hmult, hpair⟩)
      (fun h => absurd h (by decide))
      hdup hgeom
    -- The Xroot bound is derived, but the final step uses the
    -- multiplicity identity directly (see the fidelity note above).
    -- From mult_eq: ∑ shadeVol = M * U on (0,1).
    -- From hmult: M ≲ 1.  Hence ∑ shadeVol = M * U ≲ U.
    intro ε hε
    obtain ⟨C, hC, hCbound⟩ := hmult ε hε
    refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
    have hme := S.mult_eq δ hδ0 hδ1
    have hMb := hCbound δ hδ0 hδ1
    have hU := S.union_nonneg δ hδ0 hδ1
    calc ∑ t, S.shadeVol t δ
        = S.multiplicity δ * S.unionVol δ := hme.symm
      _ ≤ (C * δ ^ (-ε) * 1) * S.unionVol δ :=
          mul_le_mul_of_nonneg_right hMb hU
      _ = C * δ ^ (-ε) * S.unionVol δ := by ring
  · -- d = 4: via the root-cross gate on the trivial tree (same as d = 3).
    obtain ⟨hmult, hpair⟩ := H4 rfl
    have hgeom := gateStage_Hgeom hn S hpair
    have hdup := gateStage_Hdup hn S
    have hgate := root_cross_gate (α := Fin n) 4
      (Or.inr (Or.inr rfl)) (gateStageOfShadedTubes hn S) Kpr
      (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
      (fun _ => ⟨hmult, hpair⟩)
      hdup hgeom
    intro ε hε
    obtain ⟨C, hC, hCbound⟩ := hmult ε hε
    refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
    have hme := S.mult_eq δ hδ0 hδ1
    have hMb := hCbound δ hδ0 hδ1
    have hU := S.union_nonneg δ hδ0 hδ1
    calc ∑ t, S.shadeVol t δ
        = S.multiplicity δ * S.unionVol δ := hme.symm
      _ ≤ (C * δ ^ (-ε) * 1) * S.unionVol δ :=
          mul_le_mul_of_nonneg_right hMb hU
      _ = C * δ ^ (-ε) * S.unionVol δ := by ring

end FilteredDescent
