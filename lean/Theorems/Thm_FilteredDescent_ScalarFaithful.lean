import Theorems.Thm_FilteredDescent_FaithfulGate_Wired
import Definitions.Def_FilteredDescent_PhysicalTubes
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Scalar closure via the faithful root-cross gate (paper §13.2, (214))

This file rewires the scalar filtered-descent closure through the FAITHFUL
root-cross gate (`faithful_gate_wired`, paper §10, (135)–(153)), replacing the
old simplified `root_cross_gate` path.  The logical chain is:

* `geom_pair` (paper (53)/(177)/(81)) from the REAL per-dimension inputs
  `H2`/`H3`/`H4` (selected by `d = 2 ∨ d = 3 ∨ d = 4` at the call site), via
  the descent-data bridges `termLoad = shadeVol`, `totalLoad = ∑ shadeVol`;
* `faithful_gate_wired` — the (141)+(142) descent step: (139)/(141) proper
  predecessors via `Hpred`, (144) `Xroot = Xgeom + Xdup`, (146)+(148)
  duplicate control via the genuinely-proved R5 `terminal_hardening`, (147)
  geometric control via `geom_pair` — gives `N(δ)² ≲ B^pred(δ) · N(δ)`;
* the faithful (142) yields the scalar incidence (214) DIRECTLY: from
  `N(δ)² ≲ B^pred(δ) · N(δ)` divide by `N(δ)` (zero case by nonnegativity).
  This is the paper's (142) → (214) implication at the level of the mass
  ledger.  (The old `(130)` terminal-unweighting detour via the retained
  fraction `lamIn` and effective multiplicity `M` compensated for the WEAKER
  old gate output; it is not needed once the faithful gate supplies (142)
  itself.)
* `Xroot ≤ N²` (all terms nonneg) is proved as the standalone
  `Xroot_le_totalLoad_sq`, via the proved `totalLoad_sq_split`.

## The descent-data interface (`DescentData`)

The faithful gate consumes descent data — the history tree `T` with its
loads, the terminal-tube labeling `termTube`, the predecessor invariance
`Hpred` (paper (138), the induction hypothesis), the `(θ,j,c)` common-source
disintegration model data (paper (150)–(153)), and the two bridges
identifying the tree-side loads with the analytic tube data — which the
paper's §§6–9 construction provides for a real tube family.  Building that
data (the sticky/marked history tree, including the well-founded induction
on `(|I|, ℓ(χ), n)` (135)) is the remaining construction work and is NOT
done here: it is taken as explicit hypotheses, not constructed, and not
axiomatized.

Fidelity notes:
* The (135) well-founded labels are deliberately NOT part of the interface:
  the current faithful formalization covers the induction STEP only
  (`faithful_gate_wired`); label fields consumed by nothing would be
  decorative hypotheses.
* `B^pred` is fixed to `S.unionVol`, as in the paper's final application
  (and as in the old `GateStage`).
* `hn : 0 < n`, `lamIn`, `hlam`, `hlamSub` (present in the old
  `scalar_closure`) are DROPPED: `hn` served only the trivial-tree
  construction, and the `lamIn` retained fraction served only the old
  `(130)` compensation for the weaker gate.  Neither is consumed by the
  faithful proof, and decorative hypotheses are not kept.
* Every field of `DescentData` is consumed by the proof below; there are no
  decorative assumptions.

## Known integration blocker (pre-existing, not introduced here)

`Thm_FilteredDescent_RootCrossGate.lean` and
`Thm_FilteredDescent_FaithfulGate.lean` BOTH define
`FilteredDescent.SubpowerLE.add` (the former the same-`y` special case, the
latter the strictly more general `y₁+y₂` version), so no module can import
both chains at once — the literal reuse of `scalar_closure_of_gate` is
blocked until the older duplicate is deleted (the `FaithfulGate` version
subsumes it; its single use site at `RootCrossGate.lean:335` needs the
obvious `of_double` adjustment).  The terminal closure below is therefore
proved directly from the faithful output rather than routed through
`scalar_closure_of_gate`.
-/

namespace FilteredDescent

open MeasureTheory

/-- Descent data for one faithful filtered-descent stage (paper §§6–9).

Bundles exactly what `faithful_gate_wired` consumes, plus the two bridges
(`htermLoad`, `htotalLoad`) identifying the tree-side loads with the
analytic tube family `S`.  This is the output shape of the paper's §§6–9
sticky/marked history-tree construction; building it from a tube family
(including the (135) well-founded induction) is the remaining construction
work, explicitly NOT done here. -/
structure DescentData {n : ℕ} (S : ShadedTubes n) where
  T : Finset (List (Fin n))
  hroot : [] ∈ T
  hprefix : ∀ l ∈ T, ∀ p : List (Fin n), p <+: l → p ∈ T
  hnonroot : ∀ γ ∈ treeLeaves T, γ ≠ []
  termTube : List (Fin n) → Fin n
  load : List (Fin n) → ℝ → ℝ
  hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ
  /-- The predecessor invariance (paper (138)), the induction hypothesis. -/
  Hpred : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ a ∈ T, a ≠ [] →
    nodeAgg T (fun γ => load γ δ) a ≤ S.unionVol δ
  /-- The `(θ,j,c)` common-source disintegration model data
  (paper (150)–(153)). -/
  K : Type*
  [instFintype : Fintype K]
  [instDecEq : DecidableEq K]
  r : ℕ
  cls : Fin (treeChildren T []).card → K
  slotOf : K → Fin r
  hr : 0 < r
  w : K → Fin n → ℝ
  hw : ∀ k i, 0 ≤ w k i
  hW : ∀ k, 0 < ∑ i, w k i
  A : K → Finset (Fin r → Fin n)
  hAne : ∀ k, (A k).Nonempty
  α : K → ℝ
  hα : ∀ k, α k = retainedMass (w k) (A k)
  hαpos : ∀ k, 0 < α k
  hlink : ∀ k t δ, 0 < δ → δ < 1 →
    ∑ b ∈ Finset.univ.filter
      (fun b : Fin (treeChildren T []).card =>
        cls b = k ∧ 0 < rootChildDb T termTube load b t δ),
      rootChildDb T termTube load b t δ
      ≤ S.unionVol δ * ∑ U ∈ A k,
        (if U (slotOf k) = t then packetLaw (w k) U else 0)
  c₀ : ℝ
  hc₀ : 0 < c₀
  hquant : ∀ k (b : Fin (treeChildren T []).card) t δ, 0 < δ → δ < 1 →
    cls b = k → 0 < rootChildDb T termTube load b t δ →
    c₀ * S.unionVol δ ≤ rootChildDb T termTube load b t δ
  /-- Paper (152): the coarse-carrier count is subpower. -/
  hcard : SubpowerLE (fun _ : ℝ => (Fintype.card K : ℝ)) (fun _ => 1)
  /-- Bridge (paper (145)): terminal-tube loads are the shading volumes. -/
  htermLoad : ∀ t δ, termLoad T termTube load t δ = S.shadeVol t δ
  /-- Bridge (paper (136)/(145)): the total load is the total shading. -/
  htotalLoad : ∀ δ, totalLoad T load δ = ∑ t, S.shadeVol t δ

/-- `X^root ≤ N²`: by the proved `totalLoad_sq_split`,
`N² = (proper-predecessor pairs) + X^root`, and the proper-predecessor
pair sum is nonneg (every term is `0` or a product of nonneg leaf loads).
In the paper's picture this is the nonnegativity of the three parts of
`N² = (proper-predecessor pairs) + X^root + (diagonal)`. -/
theorem Xroot_le_totalLoad_sq {α : Type} [DecidableEq α]
    (T : Finset (List α)) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Xroot T (fun γ => load γ δ) ≤ (totalLoad T load δ) ^ 2 := by
  rw [totalLoad_sq_split T load δ]
  have hnn : 0 ≤ ∑ γ ∈ treeLeaves T, ∑ γ' ∈ treeLeaves T,
      (if treeLCA γ γ' ≠ [] then load γ δ * load γ' δ else 0) := by
    apply Finset.sum_nonneg
    intro γ hγ
    apply Finset.sum_nonneg
    intro γ' hγ'
    by_cases h : treeLCA γ γ' ≠ []
    · rw [if_pos h]
      exact mul_nonneg (hload γ hγ δ hδ0 hδ1) (hload γ' hγ' δ hδ0 hδ1)
    · rw [if_neg h]
  linarith

/-- The common-source pair hypothesis (paper (53)/(177)/(81)) for the
faithful gate, from the real per-dimension inputs: `d = 2` selects
`PlanarInput`, `d = 3` selects `StickyInput`, `d = 4` selects
`Marked4DInput`.  The three inputs share the pair-incidence shape; the
descent-data bridges rewrite `termLoad`/`totalLoad` to the tube-family
sums. -/
theorem faithful_geom_pair {n : ℕ} (S : ShadedTubes n)
    {d : ℕ} (hd : d = 2 ∨ d = 3 ∨ d = 4)
    (H2 : d = 2 → PlanarInput S.shadeVol S.unionVol)
    (H3 : d = 3 → StickyInput S.shadeVol S.unionVol)
    (H4 : d = 4 → Marked4DInput S.shadeVol S.unionVol)
    (D : DescentData S) :
    SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then
          termLoad D.T D.termTube D.load t δ * termLoad D.T D.termTube D.load t' δ
        else 0)
      (fun δ => S.unionVol δ * totalLoad D.T D.load δ) := by
  have hpair : SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0)
      (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ) := by
    rcases hd with rfl | rfl | rfl
    · exact H2 rfl
    · exact H3 rfl
    · exact H4 rfl
  have e1 : (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then
          termLoad D.T D.termTube D.load t δ * termLoad D.T D.termTube D.load t' δ
        else 0)
      = (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then S.shadeVol t δ * S.shadeVol t' δ else 0) := by
    funext δ
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro t' _
    by_cases h : t ≠ t'
    · rw [if_pos h, if_pos h, D.htermLoad t δ, D.htermLoad t' δ]
    · rw [if_neg h, if_neg h]
  have e2 : (fun δ => S.unionVol δ * totalLoad D.T D.load δ)
      = (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ) := by
    funext δ; rw [D.htotalLoad δ]
  rw [e1, e2]
  exact hpair

/-- Scalar closure via the faithful gate (paper §13.2, (214)).

From the descent data: the faithful gate (`faithful_gate_wired`, paper
§10 (135)–(153)) gives `N(δ)² ≲ B^pred(δ) · N(δ)` with
`B^pred = S.unionVol`; the bridges identify the tree load `N(δ)` with the
tube-family shading sum; dividing by `N(δ)` (zero case by nonnegativity)
yields the scalar incidence `∑_T |Y(T)| ≲ |⋃_T Y(T)|`.

Every field of `D` is consumed: the tree fields and `Hpred`/model data via
`faithful_gate_wired`, `htermLoad`/`htotalLoad` via the bridges. -/
theorem scalar_closure_faithful {d n : ℕ} (hd : d = 2 ∨ d = 3 ∨ d = 4)
    (S : ShadedTubes n)
    (H2 : d = 2 → PlanarInput S.shadeVol S.unionVol)
    (H3 : d = 3 → StickyInput S.shadeVol S.unionVol)
    (H4 : d = 4 → Marked4DInput S.shadeVol S.unionVol)
    (D : DescentData S) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol := by
  -- Paper (53)/(177)/(81): the common-source pair hypothesis.
  have hgeom_pair := faithful_geom_pair S hd H2 H3 H4 D
  -- The faithful gate (139)–(148): N(δ)² ≲ B^pred(δ) · N(δ).
  have hNL : SubpowerLE (fun δ => (totalLoad D.T D.load δ) ^ 2)
      (fun δ => S.unionVol δ * totalLoad D.T D.load δ) :=
    @faithful_gate_wired (Fin n) _ n D.T D.hroot D.hprefix D.hnonroot D.termTube
      D.load D.hload S.unionVol (fun δ hδ0 hδ1 => S.union_nonneg δ hδ0 hδ1)
      D.Hpred D.K D.instFintype D.instDecEq D.r D.cls D.slotOf D.hr D.w D.hw D.hW
      D.A D.hAne D.α D.hα D.hαpos D.hlink D.c₀ D.hc₀ D.hquant D.hcard hgeom_pair
  -- Bridges (faithful §10, (136)/(145)): tree load = tube-family shading sum.
  have hNL' : SubpowerLE (fun δ => (∑ t, S.shadeVol t δ) ^ 2)
      (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ) := by
    have e1 : (fun δ => (totalLoad D.T D.load δ) ^ 2)
        = (fun δ => (∑ t, S.shadeVol t δ) ^ 2) := by
      funext δ; rw [D.htotalLoad δ]
    have e2 : (fun δ => S.unionVol δ * totalLoad D.T D.load δ)
        = (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ) := by
      funext δ; rw [D.htotalLoad δ]
    rw [e1, e2] at hNL
    exact hNL
  -- Paper (142) → (214): divide N(δ)² ≲ B^pred(δ) · N(δ) by N(δ).
  intro ε hε
  obtain ⟨C, hC, hCbound⟩ := hNL' ε hε
  refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
  show (∑ t, S.shadeVol t δ) ≤ C * δ ^ (-ε) * S.unionVol δ
  have hbd := hCbound δ hδ0 hδ1
  simp only [] at hbd
  by_cases hS : (∑ t, S.shadeVol t δ) = 0
  · -- Zero case: 0 ≤ C · δ^(-ε) · U by nonnegativity.
    rw [hS]
    exact mul_nonneg (mul_nonneg hC (le_of_lt (Real.rpow_pos_of_pos hδ0 _)))
      (S.union_nonneg δ hδ0 hδ1)
  · -- Positive case: cancel the positive factor ∑a from both sides.
    have hSpos : 0 < ∑ t, S.shadeVol t δ :=
      lt_of_le_of_ne (Finset.sum_nonneg fun t _ => S.shade_nonneg t δ hδ0 hδ1)
        (Ne.symm hS)
    have h2 : (∑ t, S.shadeVol t δ) * (∑ t, S.shadeVol t δ)
        ≤ (C * δ ^ (-ε) * S.unionVol δ) * (∑ t, S.shadeVol t δ) := by
      have h' : (∑ t, S.shadeVol t δ) ^ 2
          ≤ (C * δ ^ (-ε) * S.unionVol δ) * (∑ t, S.shadeVol t δ) := by
        calc (∑ t, S.shadeVol t δ) ^ 2
            ≤ C * δ ^ (-ε) * (S.unionVol δ * ∑ t, S.shadeVol t δ) := hbd
          _ = (C * δ ^ (-ε) * S.unionVol δ) * (∑ t, S.shadeVol t δ) := by ring
      rwa [pow_two] at h'
    exact le_of_mul_le_mul_right h2 hSpos

/-- The physical loop: the faithful scalar closure applied to the real
physical tube model (`physicalRealization`, Lebesgue-measurable shading).
This wires the physical δ-tube family into the end-to-end chain — the
abstract `ShadedTubes` interface is discharged by genuine geometry. -/
theorem scalar_closure_physical {d n : ℕ} (hd : d = 2 ∨ d = 3 ∨ d = 4)
    (fam : TubeFamily n d) (sh : Shading fam)
    (hpos : ∀ δ, 0 < δ → δ < 1 → 0 < (volume (⋃ t, sh.Y t δ)).toReal)
    (H2 : d = 2 → PlanarInput (physicalRealization fam sh hpos).shadeVol
      (physicalRealization fam sh hpos).unionVol)
    (H3 : d = 3 → StickyInput (physicalRealization fam sh hpos).shadeVol
      (physicalRealization fam sh hpos).unionVol)
    (H4 : d = 4 → Marked4DInput (physicalRealization fam sh hpos).shadeVol
      (physicalRealization fam sh hpos).unionVol)
    (D : DescentData (physicalRealization fam sh hpos)) :
    SubpowerLE (fun δ => ∑ t, (physicalRealization fam sh hpos).shadeVol t δ)
      (physicalRealization fam sh hpos).unionVol :=
  scalar_closure_faithful hd (physicalRealization fam sh hpos) H2 H3 H4 D

end FilteredDescent
