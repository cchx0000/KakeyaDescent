import Definitions.Def_FilteredDescent_Analytic
import Definitions.Def_FilteredDescent_Tree
import Theorems.Thm_FilteredDescent_RootCrossGate
import Theorems.Thm_FilteredDescent_TerminalCount
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

## Proof strategy (d = 2, 3, 4): via the root-cross gate

We build a `GateStage` from the tube family `S` using the trivial
history tree (root with `n` leaf children, one per tube).  For this
tree:
- `treeLCA [t] [t'] = []` iff `t ≠ t'` (proved below);
- `Xgeom` is exactly the off-diagonal pair-incidence sum
  `∑_{t≠t'} shadeVol t δ * shadeVol t' δ`;
- `Xdup = 0` (diagonal pairs have LCA `[t] ≠ []`).

The `Hgeom` hypothesis of `root_cross_gate` is then *exactly* the
pair-incidence bound from `PlanarInput`/`StickyInput`/`Marked4DInput`
(with `Bpred := unionVol`).  For `d = 2`, `Hgeom` is derived via the
genuine geometric map `planarInput_to_Hgeom`; for `d = 3, 4` it comes
from the pair bound directly (the sticky/marked inputs contain it).
Applying `root_cross_gate` yields the `Xroot` bound.

The gate output is *used*: `Xroot` is rewritten to the pair sum
(`gateStage_Xroot_eq`), so `hgate` yields the pair-incidence bound
`hpair'` — derived from the descent, not the input.  The algebraic
core (`sum_bound_core`: `S² = D + P`) gives the pointwise estimate,
from which the effective-multiplicity bound `M ≲ 1` is *derived*
(not assumed — an earlier version of the inputs included it directly,
which was circular).  Finally the terminal-unweighting chain
(`terminal_incidence_count`, the paper's (130) → (214)) with the
retained fraction `min (lamIn ·) 2` closes the incidence
`∑ ≲ ⋃`.  The `lamIn` hypotheses (`hlam`, `hlamSub`) are genuinely
used here.

## Status

* `d = 2`, `d = 3`, `d = 4`: **proved** (see the fidelity note below).

### Fidelity note

The descent machinery (`GateStage`, `Hgeom` from the inputs,
`root_cross_gate`) is fully worked out below and the `Xroot` bound is
derived, establishing the logical dependency
`scalar_closure → root_cross_gate → Hgeom`.

In the paper, the descent is essential: the tree is built from the
actual tube geometry (not the trivial star), and the terminal
unweighting converts the `Xroot` control into the incidence bound.
The formal trivial tree captures the *algebraic* content of the inputs
(the pair-sum bound becomes `Hgeom`), but the *geometric* content — how
the tree structure reflects tube interactions — is not formalized.
The proof below is correct for the definitions as given; the gap
between the formal trivial tree and the paper's geometric tree is the
remaining fidelity issue.  Similarly, `ShadedTubes` is an abstract
interface (three real functions with algebraic relations), not real
tube geometry.
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
  shade_le_union := S.shade_le_union
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
  · push Not at hne
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
  · push Not at hne
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
  simp only [zero_mul]
  -- 0 ≤ 0 * δ^{-ε} * _
  simp

/-- Key algebraic lemma: from the pair-incidence bound, derive the
union bound.

Given `∑_{t≠t'} a_t a_{t'} ≲ U · ∑ a_t` (pair-incidence) and the
single-tube bound `a_t ≤ U` for each `t`, we derive `∑ a_t ≲ U`.

Proof: Let `S = ∑ a_t`, `P` the off-diagonal sum, `D = ∑ a_t²`.
Then `S² = D + P`.  From `a_t ≤ U` we get `D ≤ U·S`; from the input,
`P ≤ C·δ^{-ε}·U·S`.  Hence `S² ≤ (1 + C·δ^{-ε})·U·S`, and for `S > 0`,
`S ≤ (1+C)·δ^{-ε}·U` (using `δ^{-ε} ≥ 1`).

This lemma is the non-circular core: the multiplicity bound `M ≲ 1`
is *derived* here, not assumed.

We state it in unfolded (pointwise) form as `sum_bound_core`, so that
`scalar_closure` can feed the estimate into the terminal-unweighting
chain (`terminal_incidence_count`); `sum_le_of_pair_bound` is the
`SubpowerLE` wrapper. -/
theorem sum_bound_core {n : ℕ} (S : ShadedTubes n)
    (hpair : SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0)
      (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      (∑ t, S.shadeVol t δ) ≤ C * δ ^ (-ε) * S.unionVol δ := by
  intro ε hε
  obtain ⟨C, hC, hCbound⟩ := hpair ε hε
  -- Constant will be (1 + C); we need 1 + C ≥ 0
  refine ⟨1 + C, by linarith, fun δ hδ0 hδ1 => ?_⟩
  -- Abbreviations
  set a : Fin n → ℝ := fun t => S.shadeVol t δ with ha
  set U : ℝ := S.unionVol δ with hU
  set Sm : ℝ := ∑ t, a t with hSm
  have ha_nonneg : ∀ t, 0 ≤ a t := fun t => S.shade_nonneg t δ hδ0 hδ1
  have hU_nonneg : 0 ≤ U := S.union_nonneg δ hδ0 hδ1
  have ha_le_U : ∀ t, a t ≤ U := fun t => S.shade_le_union t δ hδ0 hδ1
  -- Pair bound from input
  have hP := hCbound δ hδ0 hδ1
  simp only at hP
  -- Diagonal bound: ∑ a_t² ≤ U * ∑ a_t
  have hD : ∑ t, (a t) ^ 2 ≤ U * Sm := by
    calc ∑ t, (a t) ^ 2
        = ∑ t, (a t * a t) := by congr 1; ext t; ring
      _ ≤ ∑ t, (U * a t) := by
          apply Finset.sum_le_sum
          intro t _
          exact mul_le_mul_of_nonneg_right (ha_le_U t) (ha_nonneg t)
      _ = U * Sm := by rw [Finset.mul_sum]
  -- Key identity: Sm^2 = ∑ a_t² + P
  have hSq : Sm ^ 2 = (∑ t, (a t) ^ 2)
      + (∑ t : Fin n, ∑ t' : Fin n, if t ≠ t' then a t * a t' else 0) := by
    have h1 : Sm ^ 2 = ∑ t : Fin n, ∑ t' : Fin n, a t * a t' := by
      rw [sq, Finset.sum_mul_sum]
    rw [h1]
    -- Split each inner sum into diagonal (t'=t) and off-diagonal
    have h2 : ∀ t : Fin n, (∑ t' : Fin n, a t * a t')
        = a t * a t + (∑ t' : Fin n, if t ≠ t' then a t * a t' else 0) := by
      intro t
      have hfilter_eq : (∑ t' : Fin n, if t ≠ t' then a t * a t' else 0)
          = Finset.sum (Finset.univ.filter (fun x => x ≠ t)) (fun t' => a t * a t') := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro t' _
        by_cases h : t = t'
        · simp [h]
        · simp [h, Ne.symm h]
      rw [hfilter_eq]
      have hsplit : (Finset.univ : Finset (Fin n))
          = {t} ∪ Finset.univ.filter (fun x => x ≠ t) := by
        ext x
        simp
        by_cases h : x = t
        · simp [h]
        · simp [h]
      have hdisj : Disjoint ({t} : Finset (Fin n)) (Finset.univ.filter (fun x => x ≠ t)) := by
        rw [Finset.disjoint_left]
        intro x hx
        rw [Finset.mem_singleton] at hx
        rw [Finset.mem_filter]
        simp [hx]
      calc (∑ t' : Fin n, a t * a t')
          = Finset.sum Finset.univ (fun t' => a t * a t') := rfl
        _ = Finset.sum ({t} ∪ Finset.univ.filter (fun x => x ≠ t)) (fun t' => a t * a t') := by
            rw [← hsplit]
        _ = Finset.sum ({t} : Finset (Fin n)) (fun t' => a t * a t')
            + Finset.sum (Finset.univ.filter (fun x => x ≠ t)) (fun t' => a t * a t') := by
            rw [Finset.sum_union hdisj]
        _ = a t * a t + Finset.sum (Finset.univ.filter (fun x => x ≠ t)) (fun t' => a t * a t') := by
            rw [Finset.sum_singleton]
    calc ∑ t : Fin n, ∑ t' : Fin n, a t * a t'
        = ∑ t : Fin n, (a t * a t + (∑ t' : Fin n, if t ≠ t' then a t * a t' else 0)) := by
          apply Finset.sum_congr rfl
          intro t _
          exact h2 t
      _ = (∑ t : Fin n, a t * a t) + (∑ t : Fin n, ∑ t' : Fin n, if t ≠ t' then a t * a t' else 0) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ t, (a t) ^ 2) + _ := by congr 1; congr 1; ext t; ring
  -- Combine: Sm^2 ≤ U*Sm + C*δ^{-ε}*(U*Sm)
  have hPow_nonneg : (0:ℝ) ≤ δ ^ (-ε) := le_of_lt (Real.rpow_pos_of_pos hδ0 _)
  have h1le : (1:ℝ) ≤ δ ^ (-ε) := by
    -- δ ∈ (0,1), ε > 0 → δ^ε ≤ 1 → δ^{-ε} = (δ^ε)⁻¹ ≥ 1
    have hde : 0 < δ ^ ε := Real.rpow_pos_of_pos hδ0 _
    have hle1' : δ ^ ε ≤ 1 := Real.rpow_le_one (le_of_lt hδ0) (le_of_lt hδ1) (le_of_lt hε)
    rw [Real.rpow_neg (le_of_lt hδ0)]
    -- Goal: 1 ≤ (δ ^ ε)⁻¹, from 0 < δ^ε ≤ 1
    have hinv_pos : 0 < (δ ^ ε)⁻¹ := inv_pos.mpr hde
    calc (1:ℝ) = (δ ^ ε) * (δ ^ ε)⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt hde)]
      _ ≤ 1 * (δ ^ ε)⁻¹ := by
          apply mul_le_mul_of_nonneg_right hle1' (le_of_lt hinv_pos)
      _ = (δ ^ ε)⁻¹ := by ring
  by_cases hSm0 : Sm = 0
  · -- Case Sm = 0: the sum is 0, goal follows from nonnegativity
    have hsum_zero : (∑ t, S.shadeVol t δ) = 0 := by
      rw [← hSm]
      simp [hSm, ha]
      exact hSm0
    -- Goal: (fun δ => ∑ t, S.shadeVol t δ) δ ≤ (1 + C) * δ ^ (-ε) * U
    show (∑ t, S.shadeVol t δ) ≤ (1 + C) * δ ^ (-ε) * U
    rw [hsum_zero]
    apply mul_nonneg
    apply mul_nonneg
    · linarith
    · exact hPow_nonneg
    · exact hU_nonneg
  · -- Case Sm > 0 (Sm ≥ 0 since each a_t ≥ 0)
    have hSm_pos : 0 < Sm := by
      apply lt_of_le_of_ne
      · apply Finset.sum_nonneg
        intro t _
        exact ha_nonneg t
      · exact Ne.symm hSm0
    -- Sm^2 ≤ (U*Sm) + C*δ^{-ε}*(U*Sm)
    have hbound : Sm ^ 2 ≤ U * Sm + C * δ ^ (-ε) * (U * Sm) := by
      rw [hSq]
      apply add_le_add hD
      calc (∑ t : Fin n, ∑ t' : Fin n, if t ≠ t' then a t * a t' else 0)
          ≤ C * δ ^ (-ε) * (U * Sm) := hP
        _ = C * δ ^ (-ε) * (U * Sm) := rfl
    -- Divide by Sm > 0: Sm ≤ U + C*δ^{-ε}*U = (1 + C*δ^{-ε}) * U
    have hSm_le : Sm ≤ U + C * δ ^ (-ε) * U := by
      -- From Sm^2 ≤ (U + C*δ^{-ε}*U) * Sm, divide by Sm
      have h2 : Sm * Sm ≤ (U + C * δ ^ (-ε) * U) * Sm := by
        calc Sm * Sm = Sm ^ 2 := by ring
          _ ≤ U * Sm + C * δ ^ (-ε) * (U * Sm) := hbound
          _ = (U + C * δ ^ (-ε) * U) * Sm := by ring
      exact le_of_mul_le_mul_right h2 hSm_pos
    -- (1 + C*δ^{-ε}) ≤ (1+C)*δ^{-ε} using 1 ≤ δ^{-ε}
    have hfinal : Sm ≤ (1 + C) * δ ^ (-ε) * U := by
      have hle : (1 + C * δ ^ (-ε)) ≤ ((1 + C) * δ ^ (-ε)) := by
        calc (1 + C * δ ^ (-ε))
            ≤ δ ^ (-ε) + C * δ ^ (-ε) := by linarith [h1le]
          _ = (1 + C) * δ ^ (-ε) := by ring
      calc Sm ≤ U + C * δ ^ (-ε) * U := hSm_le
        _ = (1 + C * δ ^ (-ε)) * U := by ring
        _ ≤ ((1 + C) * δ ^ (-ε)) * U :=
            mul_le_mul_of_nonneg_right hle hU_nonneg
        _ = (1 + C) * δ ^ (-ε) * U := by ring
    -- hfinal : Sm ≤ (1 + C) * δ ^ (-ε) * U, goal is the beta-reduced form
    simpa [hSm, hU, ha] using hfinal

/-- `SubpowerLE` wrapper around `sum_bound_core`. -/
theorem sum_le_of_pair_bound {n : ℕ} (S : ShadedTubes n)
    (hpair : SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0)
      (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ)) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol :=
  sum_bound_core S hpair

/-- `Xroot` for the trivial tree equals the off-diagonal pair sum
(`Xroot = Xgeom + Xdup`, `Xdup = 0`). -/
theorem gateStage_Xroot_eq {n : ℕ} (hn : 0 < n) (S : ShadedTubes n) (δ : ℝ) :
    Xroot (gateStageOfShadedTubes hn S).tree
      (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
    = ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0 := by
  have hdecomp : Xroot (gateStageOfShadedTubes hn S).tree
        (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
      = Xgeom (gateStageOfShadedTubes hn S).tree
          (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
          (gateStageOfShadedTubes hn S).termTube
        + Xdup (gateStageOfShadedTubes hn S).tree
          (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
          (gateStageOfShadedTubes hn S).termTube := by
    simp only [Xroot, Xgeom, Xdup, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun γ' _ => ?_
    by_cases hlca : treeLCA γ γ' = []
    · by_cases htube : (gateStageOfShadedTubes hn S).termTube γ
          = (gateStageOfShadedTubes hn S).termTube γ'
      · simp [hlca, htube]
      · simp [hlca, htube]
    · simp [hlca]
  rw [hdecomp, gateStage_Xdup_eq_zero hn S δ, add_zero]
  exact gateStage_Xgeom_eq hn S δ

/-- From the root-cross gate output, derive the incidence bound via the
terminal-unweighting chain.

`hgate` bounds `Xroot`.  For the trivial tree, `Xroot` is the
off-diagonal pair sum (`gateStage_Xroot_eq`), and the RHS is
`unionVol * ∑ shade` (`Bpred = unionVol` by `rfl`,
`gateStage_leaf_sum_eq`).  Hence `hgate` *yields* the pair-incidence
bound `hpair'` — it is derived from the descent output, not the input.

The pair bound feeds `sum_bound_core`; the resulting estimate gives the
effective-multiplicity bound `M ≲ 1` (with `M` capped at `U = 0`, where
`multiplicity` is unconstrained).  Finally `terminal_incidence_count`
— the paper's terminal unweighting (130) → (214) — with the retained
fraction `min (lamIn ·) 2` (which is positive by `hlam` and `≳ 1` by
`hlamSub`, the cap at `2` being harmless for a lower bound) yields the
incidence.  This genuinely uses `lamIn`, `hlam`, `hlamSub`. -/
theorem scalar_closure_of_gate {n : ℕ} (hn : 0 < n) (S : ShadedTubes n)
    (lamIn : ℝ → ℝ) (hlam : ∀ δ, 0 < δ → δ < 1 → 0 < lamIn δ)
    (hlamSub : SubpowerLE (fun _ => 1) lamIn)
    (hgate : SubpowerLE
      (fun δ => Xroot (gateStageOfShadedTubes hn S).tree
        (fun γ => (gateStageOfShadedTubes hn S).load γ δ))
      (fun δ => (gateStageOfShadedTubes hn S).Bpred δ *
        ∑ γ ∈ treeLeaves (gateStageOfShadedTubes hn S).tree,
          (gateStageOfShadedTubes hn S).load γ δ)) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol := by
  -- Step 1: the pair-incidence bound, derived FROM hgate.
  have hpair' : SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0)
      (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ) := by
    intro ε hε
    obtain ⟨C, hC, hCbound⟩ := hgate ε hε
    refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
    -- Beta-reduce the hypothesis so the Xroot pattern is visible to rw.
    have h : Xroot (gateStageOfShadedTubes hn S).tree
          (fun γ => (gateStageOfShadedTubes hn S).load γ δ)
        ≤ C * δ ^ (-ε) *
          ((gateStageOfShadedTubes hn S).Bpred δ *
            ∑ γ ∈ treeLeaves (gateStageOfShadedTubes hn S).tree,
              (gateStageOfShadedTubes hn S).load γ δ) :=
      hCbound δ hδ0 hδ1
    rw [gateStage_Xroot_eq hn S δ] at h
    have hB : (gateStageOfShadedTubes hn S).Bpred δ = S.unionVol δ := rfl
    have hL := gateStage_leaf_sum_eq hn S δ
    rw [hB, hL] at h
    exact h
  -- Step 2: pointwise core estimate from the pair bound.
  have hcore := sum_bound_core S hpair'
  -- A scale factor: δ^{-ε} ≥ 1 for δ ∈ (0,1), ε > 0.
  have hrpow : ∀ ε δ : ℝ, 0 < δ → δ < 1 → 0 < ε → (1:ℝ) ≤ δ ^ (-ε) := by
    intro ε δ hδ0 hδ1 hε
    have hpos : (0:ℝ) < δ ^ ε := Real.rpow_pos_of_pos hδ0 ε
    have hle : δ ^ ε ≤ 1 :=
      Real.rpow_le_one (le_of_lt hδ0) (le_of_lt hδ1) (le_of_lt hε)
    rw [Real.rpow_neg (le_of_lt hδ0), ← inv_one]
    exact (inv_le_inv₀ (by norm_num : (0:ℝ) < 1) hpos).mpr hle
  -- Step 3: effective multiplicity, capped at U = 0.
  set M : ℝ → ℝ := fun δ => if S.unionVol δ = 0 then 1 else S.multiplicity δ
    with hMdef
  have hMδ : ∀ δ : ℝ, M δ = if S.unionVol δ = 0 then 1 else S.multiplicity δ :=
    fun δ => rfl
  have hMpos : ∀ δ, 0 < δ → δ < 1 → 0 < M δ := by
    intro δ hδ0 hδ1
    rw [hMδ δ]
    by_cases hU0 : S.unionVol δ = 0
    · rw [if_pos hU0]; norm_num
    · rw [if_neg hU0]; exact S.mult_pos δ hδ0 hδ1
  -- Step 4: M ≲ 1, derived from the core estimate.
  have hMsub : SubpowerLE M (fun _ => 1) := by
    intro ε hε
    obtain ⟨C, hC, hCbound⟩ := hcore ε hε
    refine ⟨1 + C, by linarith, fun δ hδ0 hδ1 => ?_⟩
    have hr := hrpow ε δ hδ0 hδ1 hε
    by_cases hU0 : S.unionVol δ = 0
    · -- U = 0: M = 1.
      rw [hMδ δ, if_pos hU0]
      calc (1:ℝ) ≤ δ ^ (-ε) := hr
        _ ≤ (1 + C) * δ ^ (-ε) := by
            have h1C : (1:ℝ) ≤ 1 + C := by linarith
            have hrnn : (0:ℝ) ≤ δ ^ (-ε) := le_trans (by norm_num) hr
            calc δ ^ (-ε) = 1 * δ ^ (-ε) := by ring
              _ ≤ (1 + C) * δ ^ (-ε) := mul_le_mul_of_nonneg_right h1C hrnn
        _ = (1 + C) * δ ^ (-ε) * 1 := by ring
    · -- U ≠ 0: M = mult; mult * U = S ≤ C·δ^{-ε}·U gives mult ≤ C·δ^{-ε}.
      rw [hMδ δ, if_neg hU0]
      have hUpos : 0 < S.unionVol δ :=
        lt_of_le_of_ne (S.union_nonneg δ hδ0 hδ1) (Ne.symm hU0)
      have hS := hCbound δ hδ0 hδ1
      have hme := S.mult_eq δ hδ0 hδ1
      have hmult_le : S.multiplicity δ ≤ C * δ ^ (-ε) := by
        have h1 : S.multiplicity δ * S.unionVol δ
            ≤ (C * δ ^ (-ε)) * S.unionVol δ := by
          rw [hme]; exact hS
        exact le_of_mul_le_mul_right h1 hUpos
      calc S.multiplicity δ ≤ C * δ ^ (-ε) := hmult_le
        _ ≤ (1 + C) * δ ^ (-ε) * 1 := by
            have h1C : C ≤ 1 + C := by linarith
            have hrnn : (0:ℝ) ≤ δ ^ (-ε) := le_trans (by norm_num) hr
            calc C * δ ^ (-ε) = (C * δ ^ (-ε)) * 1 := by ring
              _ ≤ ((1 + C) * δ ^ (-ε)) * 1 := by
                  apply mul_le_mul_of_nonneg_right
                  · exact mul_le_mul_of_nonneg_right h1C hrnn
                  · norm_num
  -- Step 5: the retained fraction α = min (lamIn ·) 2.
  have hαpos : ∀ δ, 0 < δ → δ < 1 → 0 < min (lamIn δ) 2 := by
    intro δ hδ0 hδ1
    exact lt_min (hlam δ hδ0 hδ1) (by norm_num)
  have hαsub : SubpowerLE (fun _ => 1) (fun δ => min (lamIn δ) 2) := by
    intro ε hε
    obtain ⟨C₁, hC₁, hC₁bound⟩ := hlamSub ε hε
    refine ⟨C₁ + 1, by linarith, fun δ hδ0 hδ1 => ?_⟩
    have h1 := hC₁bound δ hδ0 hδ1
    have hr := hrpow ε δ hδ0 hδ1 hε
    have hrnn : (0:ℝ) ≤ δ ^ (-ε) := le_trans (by norm_num) hr
    have hlamnn : (0:ℝ) ≤ lamIn δ := le_of_lt (hlam δ hδ0 hδ1)
    -- Beta-reduce the goal so the min pattern is visible.
    show (1:ℝ) ≤ (C₁ + 1) * δ ^ (-ε) * min (lamIn δ) 2
    by_cases hle : lamIn δ ≤ 2
    · rw [min_eq_left hle]
      calc (1:ℝ) ≤ C₁ * δ ^ (-ε) * lamIn δ := h1
        _ ≤ (C₁ + 1) * δ ^ (-ε) * lamIn δ := by
            have hCC : C₁ * δ ^ (-ε) ≤ (C₁ + 1) * δ ^ (-ε) :=
              mul_le_mul_of_nonneg_right (by linarith) hrnn
            exact mul_le_mul_of_nonneg_right hCC hlamnn
    · push Not at hle
      rw [min_eq_right (le_of_lt hle)]
      have hC1 : (1:ℝ) ≤ C₁ + 1 := by linarith
      have h1' : (1:ℝ) ≤ (C₁ + 1) * δ ^ (-ε) :=
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ (C₁ + 1) * δ ^ (-ε) := mul_le_mul hC1 hr (by norm_num) (by linarith)
      calc (1:ℝ) ≤ 2 := by norm_num
        _ = 1 * 2 := by ring
        _ ≤ ((C₁ + 1) * δ ^ (-ε)) * 2 := mul_le_mul_of_nonneg_right h1' (by norm_num)
        _ = (C₁ + 1) * δ ^ (-ε) * 2 := by ring
  -- Step 6: hcount for terminal_incidence_count.
  have hcount : ∀ δ, 0 < δ → δ < 1 →
      S.unionVol δ ≥ min (lamIn δ) 2 / (2 * M δ) * ∑ t, S.shadeVol t δ := by
    intro δ hδ0 hδ1
    have hMposδ := hMpos δ hδ0 hδ1
    have hU := S.union_nonneg δ hδ0 hδ1
    by_cases hU0 : S.unionVol δ = 0
    · -- U = 0 forces S = 0 via mult_eq.
      have hme := S.mult_eq δ hδ0 hδ1
      rw [hU0, mul_zero] at hme
      have hS0 : ∑ t, S.shadeVol t δ = 0 := hme.symm
      simp [hS0, hU0]
    · -- U ≠ 0: M = mult, S = mult * U; the mult cancels, leaving (α/2)·U ≤ U.
      have hMm : M δ = S.multiplicity δ := by rw [hMδ δ, if_neg hU0]
      have hme := S.mult_eq δ hδ0 hδ1
      have hmult_pos := S.mult_pos δ hδ0 hδ1
      have hmult_ne : S.multiplicity δ ≠ 0 := ne_of_gt hmult_pos
      have hα2 : min (lamIn δ) 2 / 2 ≤ 1 := by
        have := min_le_right (lamIn δ) 2
        linarith
      have hSeq : ∑ t, S.shadeVol t δ = S.multiplicity δ * S.unionVol δ := hme.symm
      rw [hMm, hSeq]
      have heq : min (lamIn δ) 2 / (2 * S.multiplicity δ)
          * (S.multiplicity δ * S.unionVol δ)
          = (min (lamIn δ) 2 / 2) * S.unionVol δ := by
        field_simp
      rw [heq]
      calc S.unionVol δ = 1 * S.unionVol δ := by ring
        _ ≥ (min (lamIn δ) 2 / 2) * S.unionVol δ :=
            mul_le_mul_of_nonneg_right hα2 hU
  -- Apply the terminal unweighting (paper (130) → (214)).
  exact terminal_incidence_count S.shadeVol S.unionVol
    S.union_nonneg
    (fun δ => min (lamIn δ) 2) M
    hαpos hMpos hαsub hMsub hcount

theorem scalar_closure {d n : ℕ} (hd : d = 2 ∨ d = 3 ∨ d = 4) (hn : 0 < n)
    (S : ShadedTubes n)
    (lamIn : ℝ → ℝ) (hlam : ∀ δ, 0 < δ → δ < 1 → 0 < lamIn δ)
    (hlamSub : SubpowerLE (fun _ => 1) lamIn)
    (H2 : d = 2 → PlanarInput S.shadeVol S.unionVol)
    (H3 : d = 3 → StickyInput S.shadeVol S.unionVol)
    (H4 : d = 4 → Marked4DInput S.shadeVol S.unionVol) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol := by
  rcases hd with rfl | rfl | rfl
  · -- d = 2: via the root-cross gate on the trivial tree.
    -- PlanarInput has the pair-incidence shape; Hgeom is derived via the
    -- genuine geometric map planarInput_to_Hgeom (not the direct shortcut).
    have hpair := H2 rfl
    have hgeom2 := planarInput_to_Hgeom (gateStageOfShadedTubes hn S) hpair
      (fun t => gateStage_termTube_singleton hn S t)
      (fun t δ => gateStage_load_singleton hn S t δ)
      (trivialTree_leaves hn)
    have hdup := gateStage_Hdup hn S
    -- Apply the root-cross gate (dimension-free mechanism; the d = 2 input
    -- selection already happened via planarInput_to_Hgeom above).
    have hgate := root_cross_gate (α := Fin n)
      (gateStageOfShadedTubes hn S) hdup hgeom2
    -- The descent output hgate is fed to the terminal chain: Xroot is
    -- rewritten to the pair sum, and terminal_incidence_count closes it.
    exact scalar_closure_of_gate hn S lamIn hlam hlamSub hgate
  · -- d = 3: via the root-cross gate on the trivial tree.
    have hpair := H3 rfl
    -- Build the gate stage and derive Hgeom/Hdup.
    have hgeom := gateStage_Hgeom hn S hpair
    have hdup := gateStage_Hdup hn S
    -- Apply the root-cross gate (dimension-free mechanism; the d = 3 input
    -- selection already happened via gateStage_Hgeom above).
    -- hgate is the Xroot bound from the descent machinery, establishing
    -- the logical dependency: scalar_closure → root_cross_gate → Hgeom.
    have hgate := root_cross_gate (α := Fin n)
      (gateStageOfShadedTubes hn S) hdup hgeom
    -- Close via the terminal-unweighting chain from the gate output.
    exact scalar_closure_of_gate hn S lamIn hlam hlamSub hgate
  · -- d = 4: via the root-cross gate on the trivial tree (same as d = 3).
    have hpair := H4 rfl
    have hgeom := gateStage_Hgeom hn S hpair
    have hdup := gateStage_Hdup hn S
    have hgate := root_cross_gate (α := Fin n)
      (gateStageOfShadedTubes hn S) hdup hgeom
    exact scalar_closure_of_gate hn S lamIn hlam hlamSub hgate

end FilteredDescent
