import Definitions.Def_FilteredDescent_Analytic
import Definitions.Def_FilteredDescent_Tree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# M7 — Root-cross gate (paper (142)), d = 2, 3, 4

The root-cross gate: `X^{root} ≲ B^{pred} · ∫N`, uniformly for
`δ ∈ (0,1)`.  The duplicate part is closed by M6 (taken as the hypothesis
`Hdup`); the geometric part is the paper's per-dimension analytic
assembly, whose inputs are the explicitly named imported estimates,
selected by the dimension hypothesis:

* `d = 2`: the hereditary planar Córdoba estimate [2] (`H2`, paper (53));
* `d = 3`: the sticky Kakeya input [7,10] (`H3`, paper (177));
* `d = 4`: the uniform marked 4D sticky input [9] (`H4`, paper (81)).

Only the input matching the dimension is assumed.  The `GateStage`
bundles the history tree with the shaded tube family it is built over
(tubes indexed by the shared `Fin n`); deriving the geometric pair bound
from the selected input is the proof obligation.  `d ≥ 5` is not claimed
(the paper leaves it open), and the typed Hall-capacity route
(paper (160)/(207)) is excluded.

## Proof structure

The `Xroot = Xgeom + Xdup` decomposition is proved pointwise from the
definitions (the same case analysis as M6 `duplicate_closure`).  The
duplicate part comes from `Hdup` (M6); the geometric part comes from
`Hgeom`, which is the paper's per-dimension analytic core — formalizing
how `H2`/`H3`/`H4` imply the geometric bound is the remaining analytic
work (see the Status note below).  The two `SubpowerLE` bounds combine by
additivity of the constant.

## Status note

`Hgeom` is an explicit hypothesis, not a derived fact.  It represents the
paper's analytic core (§§5–12): deriving the `Xgeom` bound from the
dimension-specific inputs [2], [7,10], [9].  The `PlanarInput` /
`StickyInput` / `Marked4DInput` structures are recorded as `H2`/`H3`/`H4`
but the implication `H2/H3/H4 ⇒ Hgeom` is not formalized.  This is a
formalization gap, not a paper gap.
-/

namespace FilteredDescent

/-- `SubpowerLE` is closed under addition of the dominated quantity. -/
theorem SubpowerLE.add {x₁ x₂ y : ℝ → ℝ}
    (h₁ : SubpowerLE x₁ y) (h₂ : SubpowerLE x₂ y) :
    SubpowerLE (fun δ => x₁ δ + x₂ δ) y := by
  intro ε hε
  obtain ⟨C₁, hC₁, hC₁b⟩ := h₁ ε hε
  obtain ⟨C₂, hC₂, hC₂b⟩ := h₂ ε hε
  refine ⟨C₁ + C₂, by linarith, fun δ hδ0 hδ1 => ?_⟩
  have e1 := hC₁b δ hδ0 hδ1
  have e2 := hC₂b δ hδ0 hδ1
  calc x₁ δ + x₂ δ ≤ C₁ * δ ^ (-ε) * y δ + C₂ * δ ^ (-ε) * y δ :=
        add_le_add e1 e2
    _ = (C₁ + C₂) * δ ^ (-ε) * y δ := by ring

/-- LCA of a singleton with itself. -/
theorem treeLCA_singleton_self {n : ℕ} (t : Fin n) :
    treeLCA ([t] : List (Fin n)) [t] = [t] := by
  have hlen : ([t] : List (Fin n)).length = 1 := rfl
  have h1mem : 1 ∈ (Finset.range ([t].length + 1)).filter
      (fun k_ => ([t] : List (Fin n)).take k_ <+: ([t] : List (Fin n))) := by
    rw [Finset.mem_filter, Finset.mem_range, hlen]
    refine ⟨by decide, ?_⟩
    exact List.prefix_rfl
  have hle1 : ∀ x ∈ (Finset.range ([t].length + 1)).filter
      (fun k_ => ([t] : List (Fin n)).take k_ <+: ([t] : List (Fin n))), x ≤ 1 := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range, hlen] at hx
    omega
  have hmax : (((Finset.range ([t].length + 1)).filter
      (fun k_ => ([t] : List (Fin n)).take k_ <+: ([t] : List (Fin n)))).max'
      ⟨1, h1mem⟩) = 1 :=
    le_antisymm (Finset.max'_le _ _ 1 hle1) (Finset.le_max' _ _ h1mem)
  have htake : List.take 1 ([t] : List (Fin n)) = [t] := rfl
  unfold treeLCA
  rw [hmax, htake]

/-- LCA of distinct singletons is `[]`. -/
theorem treeLCA_singleton_ne {n : ℕ} {t t' : Fin n} (hne : t ≠ t') :
    treeLCA ([t] : List (Fin n)) [t'] = [] := by
  have hsing_pre : ∀ a b : Fin n, [a] <+: ([b] : List (Fin n)) → a = b := by
    intro a b h
    have := List.prefix_iff_eq_take.mp h
    simp at this
    exact this
  have hlen : ([t] : List (Fin n)).length = 1 := rfl
  have hSeq : (Finset.range ([t].length + 1)).filter
      (fun k_ => ([t] : List (Fin n)).take k_ <+: ([t'] : List (Fin n))) = {0} := by
    ext x
    rw [Finset.mem_filter, Finset.mem_range, hlen, Finset.mem_singleton]
    constructor
    · rintro ⟨hx2, hpre⟩
      by_contra hx0
      have hx1 : x = 1 := by omega
      subst hx1
      have hpre' : ([t] : List (Fin n)) <+: [t'] := by simpa using hpre
      exact hne (hsing_pre t t' hpre')
    · intro hx
      subst hx
      refine ⟨by decide, ?_⟩
      show ([t] : List (Fin n)).take 0 <+: [t']
      rw [List.take_zero]
      exact List.nil_prefix
  have h0mem : 0 ∈ (Finset.range ([t].length + 1)).filter
      (fun k_ => ([t] : List (Fin n)).take k_ <+: ([t'] : List (Fin n))) := by
    rw [Finset.mem_filter, Finset.mem_range, hlen]
    refine ⟨by decide, ?_⟩
    show ([] : List (Fin n)) <+: [t']
    exact List.nil_prefix
  have hmax0 : ((((Finset.range ([t].length + 1)).filter
      (fun k_ => ([t] : List (Fin n)).take k_ <+: ([t'] : List (Fin n)))).max'
      ⟨0, h0mem⟩) = 0) := by
    apply le_antisymm _ (Nat.zero_le _)
    apply Finset.max'_le _ _ 0
    intro x hx
    rw [hSeq, Finset.mem_singleton] at hx
    omega
  unfold treeLCA
  rw [hmax0, List.take_zero]

/-- H3 ⇒ Hgeom: the sticky Kakeya input implies the geometric bound for a
GateStage built directly from the tube family (trivial tree, one leaf per
tube, load = shading).  For such a stage, `Xgeom` is exactly the tube-pair
sum controlled by `StickyInput`. -/
theorem stickyInput_to_Hgeom {n : ℕ} (G : GateStage (Fin n) n 1)
    (h3 : StickyInput G.shadeVol G.unionVol G.multiplicity)
    (htree : G.tree = {[]} ∪ Finset.univ.image (fun t : Fin n => [t]))
    (hterm : ∀ t : Fin n, G.termTube [t] = t)
    (hload : ∀ t : Fin n, ∀ δ : ℝ, G.load [t] δ = G.shadeVol t δ)
    (hleaves : treeLeaves G.tree = Finset.univ.image (fun t : Fin n => [t])) :
    SubpowerLE (fun δ => Xgeom G.tree (fun γ => G.load γ δ) G.termTube)
      (fun δ => G.unionVol δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ) := by
  -- The map t ↦ [t] is injective
  have hinj : Function.Injective (fun t : Fin n => [t]) := by
    intro t₁ t₂ h
    simp at h
    exact h
  have hinjOn : Set.InjOn (fun t : Fin n => [t]) (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) :=
    hinj.injOn
  -- Reindex Xgeom: for the trivial tree, LCA([t],[t']) = [] iff t ≠ t'
  have hXgeom_eq : ∀ δ : ℝ,
      Xgeom G.tree (fun γ => G.load γ δ) G.termTube
        = ∑ t : Fin n, ∑ t' : Fin n,
            if t ≠ t' then G.shadeVol t δ * G.shadeVol t' δ else 0 := by
    intro δ
    have h1 : Xgeom G.tree (fun γ => G.load γ δ) G.termTube
        = ∑ t : Fin n, ∑ γ' ∈ treeLeaves G.tree,
            if treeLCA [t] γ' = [] ∧ G.termTube [t] ≠ G.termTube γ'
            then G.load [t] δ * G.load γ' δ else 0 := by
      simp only [Xgeom, hleaves]
      rw [Finset.sum_image hinjOn]
    rw [h1]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h2 : (∑ γ' ∈ treeLeaves G.tree,
            if treeLCA [t] γ' = [] ∧ G.termTube [t] ≠ G.termTube γ'
            then G.load [t] δ * G.load γ' δ else 0)
        = ∑ t' : Fin n,
            if t ≠ t' then G.shadeVol t δ * G.shadeVol t' δ else 0 := by
      rw [hleaves, Finset.sum_image hinjOn]
      refine Finset.sum_congr rfl fun t' _ => ?_
      by_cases hne : t ≠ t'
      · have hlca := treeLCA_singleton_ne hne
        simp [hlca, hterm t, hterm t', hne, hload t δ, hload t' δ]
      · push_neg at hne
        subst hne
        have hlca := treeLCA_singleton_self t
        simp [hlca]
    rw [h2]
  -- Reindex ∑ loads
  have hsum_eq : ∀ δ : ℝ,
      ∑ γ ∈ treeLeaves G.tree, G.load γ δ = ∑ t : Fin n, G.shadeVol t δ := by
    intro δ
    rw [hleaves, Finset.sum_image hinjOn]
    refine Finset.sum_congr rfl fun t _ => hload t δ
  -- Apply StickyInput (second component: pair-incidence bound)
  -- Unfold StickyInput to extract the pair-incidence bound
  simp only [StickyInput] at h3
  obtain ⟨_, hpair⟩ := h3
  intro ε hε
  obtain ⟨C, hC, hCbound⟩ := hpair ε hε
  refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
  have e1 := hCbound δ hδ0 hδ1
  -- Rewrite the goal using the reindexing lemmas
  have hgoal : Xgeom G.tree (fun γ => G.load γ δ) G.termTube
      ≤ C * δ ^ (-ε) * (G.unionVol δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ) := by
    rw [hXgeom_eq δ, hsum_eq δ]
    -- Now the goal matches e1 after beta reduction
    simpa using e1
  -- The goal is definitionally equal to hgoal after beta reduction
  simpa using hgoal

/-- H4 ⇒ Hgeom: same as above for the marked 4D input. -/
theorem marked4DInput_to_Hgeom {n : ℕ} (G : GateStage (Fin n) n 1)
    (h4 : Marked4DInput G.shadeVol G.unionVol G.multiplicity)
    (htree : G.tree = {[]} ∪ Finset.univ.image (fun t : Fin n => [t]))
    (hterm : ∀ t : Fin n, G.termTube [t] = t)
    (hload : ∀ t : Fin n, ∀ δ : ℝ, G.load [t] δ = G.shadeVol t δ)
    (hleaves : treeLeaves G.tree = Finset.univ.image (fun t : Fin n => [t])) :
    SubpowerLE (fun δ => Xgeom G.tree (fun γ => G.load γ δ) G.termTube)
      (fun δ => G.unionVol δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ) := by
  -- Same proof as stickyInput_to_Hgeom; Marked4DInput has the same shape.
  have hinj : Function.Injective (fun t : Fin n => [t]) := by
    intro t₁ t₂ h
    simp at h
    exact h
  have hinjOn : Set.InjOn (fun t : Fin n => [t]) (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) :=
    hinj.injOn
  have hXgeom_eq : ∀ δ : ℝ,
      Xgeom G.tree (fun γ => G.load γ δ) G.termTube
        = ∑ t : Fin n, ∑ t' : Fin n,
            if t ≠ t' then G.shadeVol t δ * G.shadeVol t' δ else 0 := by
    intro δ
    have h1 : Xgeom G.tree (fun γ => G.load γ δ) G.termTube
        = ∑ t : Fin n, ∑ γ' ∈ treeLeaves G.tree,
            if treeLCA [t] γ' = [] ∧ G.termTube [t] ≠ G.termTube γ'
            then G.load [t] δ * G.load γ' δ else 0 := by
      simp only [Xgeom, hleaves]
      rw [Finset.sum_image hinjOn]
    rw [h1]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h2 : (∑ γ' ∈ treeLeaves G.tree,
            if treeLCA [t] γ' = [] ∧ G.termTube [t] ≠ G.termTube γ'
            then G.load [t] δ * G.load γ' δ else 0)
        = ∑ t' : Fin n,
            if t ≠ t' then G.shadeVol t δ * G.shadeVol t' δ else 0 := by
      rw [hleaves, Finset.sum_image hinjOn]
      refine Finset.sum_congr rfl fun t' _ => ?_
      by_cases hne : t ≠ t'
      · have hlca := treeLCA_singleton_ne hne
        simp [hlca, hterm t, hterm t', hne, hload t δ, hload t' δ]
      · push_neg at hne
        subst hne
        have hlca := treeLCA_singleton_self t
        simp [hlca]
    rw [h2]
  have hsum_eq : ∀ δ : ℝ,
      ∑ γ ∈ treeLeaves G.tree, G.load γ δ = ∑ t : Fin n, G.shadeVol t δ := by
    intro δ
    rw [hleaves, Finset.sum_image hinjOn]
    refine Finset.sum_congr rfl fun t _ => hload t δ
  -- Apply Marked4DInput (second component: pair-incidence bound)
  simp only [Marked4DInput] at h4
  obtain ⟨_, hpair⟩ := h4
  intro ε hε
  obtain ⟨C, hC, hCbound⟩ := hpair ε hε
  refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
  have e1 := hCbound δ hδ0 hδ1
  have hgoal : Xgeom G.tree (fun γ => G.load γ δ) G.termTube
      ≤ C * δ ^ (-ε) * (G.unionVol δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ) := by
    rw [hXgeom_eq δ, hsum_eq δ]
    simpa using e1
  simpa using hgoal

theorem root_cross_gate {α : Type} [DecidableEq α] {n m : ℕ}
    (d : ℕ) (hd : d = 2 ∨ d = 3 ∨ d = 4)
    (G : GateStage α n m)
    (Kpr : ℝ → ℝ) (H2 : d = 2 → PlanarInput Kpr)
    (H3 : d = 3 → StickyInput G.shadeVol G.unionVol G.multiplicity)
    (H4 : d = 4 → Marked4DInput G.shadeVol G.unionVol G.multiplicity)
    (Hdup :
      SubpowerLE (fun δ => Xdup G.tree (fun γ => G.load γ δ) G.termTube)
        (fun δ => G.Bpred δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ))
    (Hgeom :
      SubpowerLE (fun δ => Xgeom G.tree (fun γ => G.load γ δ) G.termTube)
        (fun δ => G.Bpred δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ)) :
    SubpowerLE (fun δ => Xroot G.tree (fun γ => G.load γ δ))
      (fun δ => G.Bpred δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ) := by
  -- Pointwise decomposition: Xroot = Xgeom + Xdup (same case analysis as M6)
  have hdecomp : ∀ δ : ℝ,
      Xroot G.tree (fun γ => G.load γ δ)
        = Xgeom G.tree (fun γ => G.load γ δ) G.termTube
          + Xdup G.tree (fun γ => G.load γ δ) G.termTube := by
    intro δ
    simp only [Xroot, Xgeom, Xdup, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun γ' _ => ?_
    by_cases hlca : treeLCA γ γ' = []
    · by_cases htube : G.termTube γ = G.termTube γ'
      · simp [hlca, htube]
      · simp [hlca, htube]
    · simp [hlca]
  -- Combine the two SubpowerLE bounds by additivity
  have hadd := SubpowerLE.add Hgeom Hdup
  -- Rewrite Xroot as the sum and apply
  have heq : (fun δ => Xroot G.tree (fun γ => G.load γ δ))
      = (fun δ => Xgeom G.tree (fun γ => G.load γ δ) G.termTube
          + Xdup G.tree (fun γ => G.load γ δ) G.termTube) := by
    funext δ
    exact hdecomp δ
  rw [heq]
  exact hadd

end FilteredDescent
