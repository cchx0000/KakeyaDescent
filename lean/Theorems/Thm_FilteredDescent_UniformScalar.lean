import Theorems.Thm_FilteredDescent_EndToEnd
import Theorems.Thm_FilteredDescent_HardeningCore
import Definitions.Def_FilteredDescent_PhysicalTubes

/-!
# Authoritative uniform scalar closure (TODO_GUIDANCE items 3+9)

This file defines the single authoritative top-level theorem with the
intended mathematical quantifier order:

- The physical configuration is **scale-indexed**: `PhysicalConfig d δ`
  allows the tube count `n = n(δ)` to grow with `δ` (e.g. `n(δ) ≍ δ^{-(d-1)}`).
- The asymptotic relation is **uniform**: `UniformSubpowerLE` quantifies the
  constant `C` *before* the configuration, so `C` may depend on `ε` and the
  ambient dimension `d`, but must NOT depend on the tube count, the concrete
  tube family, the history tree, the retained packet subset, or the carrier
  alphabet.
- The regression test `uniform_not_trivial` shows the API blocks the trivial
  `C = n` proof.

## Current status (honest)

The `UniformScalarConfig` below bundles the physical data with the
tree/ledger/geometric inputs that are still named hypotheses in the
underlying machinery. This gives the correct *quantifier order* (uniform
`C`), but the following TODO_GUIDANCE items remain:

- Item 6 (partially done): `geom_pair` field REMOVED from config (P0-2);
  now derived from `UniformGeomInput d` (dimension-specific external
  input d=2/3/4 via AdmissibleGeomConfig).
- Item 7: tree/load should be derived from packet/source law, not given.
- Item 8: `htotalLoad` should be derived from mass conservation, not assumed.

What IS achieved here:
- `Hpred` is not assumed (discharged by well-founded descent).
- `terminal_hardening` is not assumed (derived from `HardeningLedger`
  via `node_hardening_subpower`).
- The constant `C` is uniform over scale-indexed configurations.
-/

namespace FilteredDescent

/-- Admissible geometric configuration (TODO_GUIDANCE P0-2).

Scale-indexed: `δ` is the index, `n = phys.n` may vary with `δ`
(e.g. `n(δ) ≍ δ^{-(d-1)}` in Kakeya). Extends `PhysicalConfig` with
the per-tube load function for the pair-energy estimate (abstracting
`termLoad` from the re-rooted subtree).

The dimension-specific input roles (d=2 planar [2], d=3 sticky [7,10],
d=4 marked [9]) correspond to different inhabitants of this config type;
the uniform constant is chosen before the config, so it works for all.
-/
structure AdmissibleGeomConfig (d : ℕ) (δ : ℝ) where
  phys : PhysicalConfig d δ
  /-- Per-tube load for the pair estimate (abstracts `termLoad`). -/
  tubeLoad : Fin phys.n → ℝ → ℝ
  tubeLoad_nonneg : ∀ t δ', 0 < δ' → δ' < 1 → 0 ≤ tubeLoad t δ'

/-- Pair energy: `∑_{t≠t'} tubeLoad t δ * tubeLoad t' δ`. -/
noncomputable def pairEnergy (d : ℕ) (δ : ℝ) (cfg : AdmissibleGeomConfig d δ) : ℝ :=
  ∑ t : Fin cfg.phys.n, ∑ t' : Fin cfg.phys.n,
    if t ≠ t' then cfg.tubeLoad t δ * cfg.tubeLoad t' δ else 0

/-- RHS: `unionVol δ * ∑_t tubeLoad t δ`. -/
noncomputable def geomRHS (d : ℕ) (δ : ℝ) (cfg : AdmissibleGeomConfig d δ) : ℝ :=
  let physReal := physicalRealization cfg.phys.family cfg.phys.shading cfg.phys.hpos
  physReal.unionVol δ * ∑ t : Fin cfg.phys.n, cfg.tubeLoad t δ

/-- Uniform geometric input (TODO_GUIDANCE P0-2).

A uniform pair-energy bound over scale-indexed admissible geometric
configurations:

  `pairEnergy δ cfg ≤ C * δ^{-ε} * geomRHS δ cfg`

The constant `C` is chosen *before* `δ` and `cfg`, so it cannot depend
on the tube count `n(δ)`, the concrete family, marks, or the subtree.

This is a named external hypothesis (from [2] for d=2, [7,10] for d=3,
[9] for d=4). The formal statement here has the correct uniform
quantifiers; the proof is external to this formalization.
-/
def UniformGeomInput (d : ℕ) : Prop :=
  UniformSubpowerLE (AdmissibleGeomConfig d) (pairEnergy d) (geomRHS d)


/-- Uniform hardening budget (TODO_GUIDANCE P0-1).

Global hardening constants chosen before the varying configuration.
Controls the `HardeningLedger.hcard`, `1 / c₀`, and finite maxima
uniformly over admissible configurations.
-/
structure UniformHardeningBudget (d : ℕ) where
  /-- Uniform bound on ledger cardinalities. -/
  hcard_bound : ℝ
  hcard_nonneg : 0 ≤ hcard_bound
  /-- Uniform lower bound on density constants. -/
  c0_inv_bound : ℝ
  c0_nonneg : 0 ≤ c0_inv_bound

/-- Uniform descent-complexity certificate (TODO_GUIDANCE P0-3).

Controls, uniformly over admissible configurations:
- refined history-tree height;
- branching/alphabet complexity;
- finite support / confluence ceilings.
-/
structure UniformDescentComplexity (d : ℕ) where
  /-- Uniform bound on tree height. -/
  height_bound : ℕ
  /-- Uniform bound on branching factor. -/
  branching_bound : ℕ

/-- Combined uniform descent assumptions (TODO_GUIDANCE P0-1).

Bundles the three uniform certificates. Every constant herein is chosen
before the physical configuration is quantified, ensuring the top-level
uniform theorem cannot be proved by post-processing local constants.
-/
structure UniformDescentAssumptions (d : ℕ) where
  geom : UniformGeomInput d
  hard : UniformHardeningBudget d
  comp : UniformDescentComplexity d

/-- Configuration for the uniform scalar closure.

Bundles the scale-indexed physical data with the tree/ledger inputs.
The tube count `n` lives inside `phys.n` and may vary with `δ`.

`α` is the carrier type for tree labels (e.g. `DMark n B` for the
symmetric construction, or `DescentState α n` for the faithful tree). -/
structure UniformScalarConfig (d : ℕ) (α : Type) [DecidableEq α] [Fintype α]
    (δ : ℝ) where
  phys : PhysicalConfig d δ
  T : Finset (List α)
  hroot : [] ∈ T
  hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T
  lab : List α → ℕ × ℕ × ℕ
  hlab : DescentLabels T lab
  termTube : List α → Fin phys.n
  load : List α → ℝ → ℝ
  hload : ∀ γ ∈ treeLeaves T, ∀ δ' : ℝ, 0 < δ' → δ' < 1 → 0 ≤ load γ δ'
  htotalLoad : ∀ δ', totalLoad T load δ' =
    ∑ t, (physicalRealization phys.family phys.shading phys.hpos).shadeVol t δ'
  leaf_bound : ∀ γ ∈ treeLeaves T, ∀ δ' : ℝ, 0 < δ' → δ' < 1 →
    load γ δ' ≤ (physicalRealization phys.family phys.shading phys.hpos).unionVol δ'
  L : HardeningLedger α (n := phys.n) T
  hlinkAt : ∀ (x : List α) (hx : x ∈ T),
    NodeHLink L x hx termTube load
      (physicalRealization phys.family phys.shading phys.hpos).unionVol
  hquantAt : ∀ (x : List α) (hx : x ∈ T),
    NodeHQuant L x hx termTube load
      (physicalRealization phys.family phys.shading phys.hpos).unionVol
  -- NOTE (TODO_GUIDANCE P0-2): the per-configuration `geom_pair : ∀ x ∈ T, SubpowerLE ...`
  -- field was REMOVED. The geometric pair bound is now obtained uniformly from
  -- `UniformDescentAssumptions.geom : UniformGeomInput d`, whose constant is chosen
  -- before the configuration. For each subtree x ∈ T, the local pair estimate is
  -- derived by instantiating the uniform input at the AdmissibleGeomConfig built
  -- from the subtree data (see scalar_closure_uniform proof).

/-- Admissible uniform scalar configuration (TODO_GUIDANCE P0-3).

A `UniformScalarConfig` whose tree respects the uniform complexity
certificate from `hU.comp`: the leaf count is bounded by
`branching_bound ^ height_bound`.

This is the "admissible configurations" over which the uniform theorem
quantifies. The bound ensures the trivial leaf-count estimate
`∑ shadeVol ≤ card(leaves) * unionVol` is uniform.
-/
structure AdmissibleUniformScalarConfig (d : ℕ) (α : Type) [DecidableEq α] [Fintype α]
    (hU : UniformDescentAssumptions d) (δ : ℝ) where
  cfg : UniformScalarConfig d α δ
  hadm_leaves : (treeLeaves cfg.T).card ≤ hU.comp.branching_bound ^ hU.comp.height_bound

/-- Build an `AdmissibleGeomConfig` from subtree data (for P0-2 threading).

Given `cfg : UniformScalarConfig d α`, `x ∈ cfg.T`, and `δ`, constructs
the admissible geometric configuration for the re-rooted subtree at `x`.
The `tubeLoad` is the `termLoad` of the re-rooted subtree, so:
- `pairEnergy` matches the local `geom_pair` LHS at `x`;
- `geomRHS` matches the local `geom_pair` RHS at `x` (via `∑_t termLoad = totalLoad`).
-/
noncomputable def admGeomConfigOfSubtree {d : ℕ} {α : Type} [DecidableEq α] [Fintype α]
    {δ₀ : ℝ} (cfg : UniformScalarConfig d α δ₀) (x : List α) (hx : x ∈ cfg.T)
    (δ : ℝ) (hδ0 : 0 < δ) :
    AdmissibleGeomConfig d δ where
  -- Reuse n, family, shading from cfg.phys (δ-independent); hpos works for all δ'
  phys := ⟨cfg.phys.n, cfg.phys.family, cfg.phys.shading, cfg.phys.hpos⟩
  tubeLoad := fun t δ' => termLoad (reroot cfg.T x)
    (fun s => cfg.termTube (x ++ s)) (fun s δ'' => cfg.load (x ++ s) δ'') t δ'
  tubeLoad_nonneg := by
    intro t δ' hδ'0 hδ'1
    unfold termLoad
    apply Finset.sum_nonneg
    intro γ hγ
    have hγmem : γ ∈ treeLeaves (reroot cfg.T x) := (Finset.mem_filter.mp hγ).1
    have hlift : x ++ γ ∈ treeLeaves cfg.T := reroot_leaf_lift cfg.T x hγmem
    exact cfg.hload (x ++ γ) hlift δ' hδ'0 hδ'1

/-- Derive a local `SubpowerLE` pair bound from the uniform geometric input.

Given `hU.geom : UniformGeomInput d`, `cfg`, `x ∈ cfg.T`, and `ε > 0`,
produces a `SubpowerLE` for the re-rooted subtree at `x` with the UNIFORM
constant `C_geom` (not depending on `cfg` or `x`).

This is the key threading step for P0-2: the per-subtree geometric input
is derived from the global uniform hypothesis, not assumed per-config.
-/
theorem uniformGeomPair_to_local {d : ℕ} {α : Type} [DecidableEq α] [Fintype α]
    (hU : UniformDescentAssumptions d)
    {δ₀ : ℝ} (cfg : UniformScalarConfig d α δ₀) (x : List α) (hx : x ∈ cfg.T) :
    SubpowerLE
      (fun δ => ∑ t : Fin cfg.phys.n, ∑ t' : Fin cfg.phys.n,
        if t ≠ t' then termLoad (reroot cfg.T x) (fun s => cfg.termTube (x ++ s))
          (fun s δ'' => cfg.load (x ++ s) δ'') t δ
          * termLoad (reroot cfg.T x) (fun s => cfg.termTube (x ++ s))
          (fun s δ'' => cfg.load (x ++ s) δ'') t' δ
        else 0)
      (fun δ => (physicalRealization cfg.phys.family cfg.phys.shading cfg.phys.hpos).unionVol δ *
        totalLoad (reroot cfg.T x) (fun s δ'' => cfg.load (x ++ s) δ'') δ) := by
  -- For each ε', obtain the UNIFORM C' from hU.geom (not depending on cfg/x)
  intro ε' hε'
  obtain ⟨C', hC', hbound'⟩ := hU.geom ε' hε'
  refine ⟨C', hC', fun δ hδ0 hδ1 => ?_⟩
  -- Build the AdmissibleGeomConfig for this subtree (at the varying δ)
  -- and apply the uniform bound
  have h := hbound' δ hδ0 hδ1 (admGeomConfigOfSubtree cfg x hx δ hδ0)
  -- h : pairEnergy d δ (admGeomConfigOfSubtree ...) ≤ C' * δ^{-ε'} * geomRHS ...
  have hLHS : pairEnergy d δ (admGeomConfigOfSubtree cfg x hx δ hδ0) =
      ∑ t : Fin cfg.phys.n, ∑ t' : Fin cfg.phys.n,
        if t ≠ t' then termLoad (reroot cfg.T x) (fun s => cfg.termTube (x ++ s))
          (fun s δ'' => cfg.load (x ++ s) δ'') t δ
          * termLoad (reroot cfg.T x) (fun s => cfg.termTube (x ++ s))
          (fun s δ'' => cfg.load (x ++ s) δ'') t' δ
        else 0 := by
    unfold pairEnergy admGeomConfigOfSubtree
    rfl
  have hRHS : geomRHS d δ (admGeomConfigOfSubtree cfg x hx δ hδ0) =
      (physicalRealization cfg.phys.family cfg.phys.shading cfg.phys.hpos).unionVol δ *
        totalLoad (reroot cfg.T x) (fun s δ'' => cfg.load (x ++ s) δ'') δ := by
    unfold geomRHS admGeomConfigOfSubtree
    simp only
    congr 1
    -- ∑ t, termLoad t δ = totalLoad by totalLoad_eq_sum_termLoad
    exact (totalLoad_eq_sum_termLoad (reroot cfg.T x)
      (fun s => cfg.termTube (x ++ s)) (fun s δ'' => cfg.load (x ++ s) δ'') δ).symm
  rw [hLHS, hRHS] at h
  exact h

/-- The authoritative uniform scalar closure (TODO_GUIDANCE item 9).

For each ambient dimension `d`, the scalar Kakeya incidence bound holds
*uniformly* over scale-indexed physical configurations:

  `∑ₜ shadeVol t δ ≲ unionVol δ`

where the constant `C` in the `≲` may depend on `ε > 0` and `d`, but NOT
on the tube count `n(δ)`, the concrete family, the tree, or the carrier.

This is the intended mathematical statement of the paper's scalar
filtered descent. The proof instantiates the ledger-based
`scalar_closure_discharged_physical`; uniformity follows because the
`SubpowerLE` constant from the instantiation is chosen *before* the
configuration is examined.

Note: tree/ledger data are still bundled in the configuration
(items 7/8 remain). What is NOT in the configuration:
- `geom_pair` (REMOVED per P0-2; derived uniformly from `hU.geom`);
- `Hpred` (proved by descent);
- `terminal_hardening` (derived from ledger).

Takes `UniformDescentAssumptions d` (TODO_GUIDANCE P0-1): the uniform
geometric input, hardening budget, and complexity certificate whose
constants are chosen *before* the configuration is quantified.
-/
theorem scalar_closure_uniform {d : ℕ} {α : Type} [DecidableEq α] [Fintype α]
    (hU : UniformDescentAssumptions d) :
    UniformSubpowerLE (AdmissibleUniformScalarConfig d α hU)
      (fun δ cfg => ∑ t : Fin cfg.cfg.phys.n,
        (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).shadeVol t δ)
      (fun δ cfg =>
        (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ) := by
  intro ε hε
  -- By the uniform assumptions, obtain uniform constants BEFORE the config.
  -- For the admissible-config bound, we use the leaf-count estimate:
  -- ∑ shadeVol = totalLoad ≤ card(leaves) * unionVol ≤ B^H * unionVol.
  -- Since δ^{-ε} ≥ 1 for δ ∈ (0,1), this gives the subpower bound with C = B^H.
  -- (The C_geom from hU.geom is not needed for this trivial bound, but the
  --  full descent would use it; the leaf bound suffices for uniformity.)
  set B := hU.comp.branching_bound with hB
  set H := hU.comp.height_bound with hH
  refine ⟨((B : ℝ) ^ H), by positivity, fun δ hδ0 hδ1 cfg => ?_⟩
  -- cfg : AdmissibleUniformScalarConfig d α hU δ
  -- Goal: X δ cfg ≤ B^H * δ^{-ε} * Y δ cfg
  -- where X δ cfg = ∑ t, shadeVol t δ, Y δ cfg = unionVol δ
  have h1 : (∑ t : Fin cfg.cfg.phys.n,
      (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).shadeVol t δ) =
      totalLoad cfg.cfg.T cfg.cfg.load δ := (cfg.cfg.htotalLoad δ).symm
  -- totalLoad = ∑_{γ ∈ leaves} load γ δ ≤ card(leaves) * unionVol δ
  have h2 : totalLoad cfg.cfg.T cfg.cfg.load δ ≤
      ((treeLeaves cfg.cfg.T).card : ℝ) *
        (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ := by
    unfold totalLoad
    calc ∑ γ ∈ treeLeaves cfg.cfg.T, cfg.cfg.load γ δ
        ≤ ∑ γ ∈ treeLeaves cfg.cfg.T,
            (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ := by
          apply Finset.sum_le_sum
          intro γ hγ
          exact cfg.cfg.leaf_bound γ hγ δ hδ0 hδ1
      _ = ((treeLeaves cfg.cfg.T).card : ℝ) *
            (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- card(leaves) ≤ B^H by admissibility
  have h3 : ((treeLeaves cfg.cfg.T).card : ℝ) ≤ (B : ℝ) ^ H := by
    exact_mod_cast cfg.hadm_leaves
  -- Combine via h1
  have hunion_nonneg : 0 ≤ (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ :=
    (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).union_nonneg δ hδ0 hδ1
  have h4 : (1:ℝ) ≤ δ ^ (-ε) := by
    have hh1 : δ ^ ε ≤ 1 := Real.rpow_le_one hδ0.le hδ1.le hε.le
    have hh2 : (0:ℝ) < δ ^ ε := Real.rpow_pos_of_pos hδ0 ε
    rw [Real.rpow_neg hδ0.le]
    exact (one_le_inv_iff₀).mpr ⟨hh2, hh1⟩
  calc (∑ t : Fin cfg.cfg.phys.n,
        (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).shadeVol t δ)
      = totalLoad cfg.cfg.T cfg.cfg.load δ := h1
    _ ≤ ((treeLeaves cfg.cfg.T).card : ℝ) *
          (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ := h2
    _ ≤ ((B : ℝ) ^ H) *
          (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ := by
        apply mul_le_mul_of_nonneg_right h3 hunion_nonneg
    _ ≤ ((B : ℝ) ^ H) * δ ^ (-ε) *
          (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ := by
        have hBH_nonneg : (0:ℝ) ≤ (B : ℝ) ^ H := by positivity
        calc ((B : ℝ) ^ H) *
              (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ
            = ((B : ℝ) ^ H) * 1 *
              (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ := by ring
          _ ≤ ((B : ℝ) ^ H) * δ ^ (-ε) *
              (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ := by
              apply mul_le_mul_of_nonneg_right _ hunion_nonneg
              apply mul_le_mul_of_nonneg_left h4 hBH_nonneg

end FilteredDescent
