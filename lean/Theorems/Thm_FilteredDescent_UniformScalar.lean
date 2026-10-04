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

/-- Admissible geometric configuration (TODO_GUIDANCE P0-2, P0-3 new).

Scale-indexed: `δ` is the index, `n = phys.n` may vary with `δ`
(e.g. `n(δ) ≍ δ^{-(d-1)}` in Kakeya).

P0-3 FIX: The old version had an arbitrary `tubeLoad : Fin n → ℝ → ℝ`
with no source compatibility, making `UniformGeomInput` uninhabited
(scaling `tubeLoad` by λ gives `pairEnergy ~ λ²` but `geomRHS ~ λ`).
Now the load is DERIVED from the physical source (`phys.shading`)
via `physicalRealization`, so it belongs to the paper's class:
actual shaded tube families and their source-restricted descendants.

The dimension-specific input roles (d=2 planar [2], d=3 sticky [7,10],
d=4 marked [9]) correspond to different inhabitants of this config type;
the uniform constant is chosen before the config, so it works for all.
-/
structure AdmissibleGeomConfig (d : ℕ) (δ : ℝ) where
  phys : PhysicalConfig d δ
  -- NOTE (P0-3): NO arbitrary tubeLoad field. The pair energy is computed
  -- from phys.shading via physicalRealization.shadeVol, ensuring the load
  -- belongs to the paper's admissible class (source-derived, not arbitrary).
  -- Subtree restriction (P0-4) constructs a restricted PhysicalConfig.

/-- Pair energy from the source shading: `∑_{t≠t'} shadeVol t δ * shadeVol t' δ`. -/
noncomputable def pairEnergy (d : ℕ) (δ : ℝ) (cfg : AdmissibleGeomConfig d δ) : ℝ :=
  let physReal := physicalRealization cfg.phys.family cfg.phys.shading cfg.phys.hpos
  ∑ t : Fin cfg.phys.n, ∑ t' : Fin cfg.phys.n,
    if t ≠ t' then physReal.shadeVol t δ * physReal.shadeVol t' δ else 0

/-- RHS from the source shading: `unionVol δ * ∑_t shadeVol t δ`. -/
noncomputable def geomRHS (d : ℕ) (δ : ℝ) (cfg : AdmissibleGeomConfig d δ) : ℝ :=
  let physReal := physicalRealization cfg.phys.family cfg.phys.shading cfg.phys.hpos
  physReal.unionVol δ * ∑ t : Fin cfg.phys.n, physReal.shadeVol t δ

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

/-- Ledger-budget compatibility (TODO_GUIDANCE P0-6).

A local `HardeningLedger` is compatible with the uniform budget if:
- its carrier count `card K` is bounded by `hcard_bound` (uniformly);
- its inverse density `1 / c₀` is bounded by `c0_inv_bound` (uniformly).

This prevents a local ledger with arbitrarily huge alphabet or tiny `c₀`
from entering an admissible uniform configuration without paying the
approved subpower loss.
-/
def LedgerBudgetCompatible {d : ℕ} {α : Type} [DecidableEq α] {n : ℕ}
    {T : Finset (List α)} (L : HardeningLedger α (n := n) T)
    (budget : UniformHardeningBudget d) : Prop :=
  (Fintype.card L.K : ℝ) ≤ budget.hcard_bound ∧
  1 / L.c₀ ≤ budget.c0_inv_bound

/-- Uniform descent-complexity certificate (TODO_GUIDANCE P0-2 new).

Paper-faithful: complexity quantities (history height H_{I,k},
support/confluence/Cartan bookkeeping, carrier counts, finite maxima)
are controlled by uniform SUBPOWER estimates (δ^{-o(1)}), NOT by fixed
natural-number bounds.

The old fixed `height_bound : ℕ` / `branching_bound : ℕ` was too strong:
it forbade the number of histories/leaves from growing with δ^{-1},
while the paper allows such growth provided structural losses remain
δ^{-o(1)}.

Full formalization of the paper's exact complexity quantities is deferred;
this placeholder records the correct specification shape.
-/
structure UniformDescentComplexity (d : ℕ) where
  /-- Placeholder: the paper's subpower complexity control.
  To be replaced by the exact quantities from §§6-9 (history height,
  support/confluence/Cartan, etc.) with uniform subpower bounds. -/
  placeholder : True := trivial

/-- Uniform separation bound (TODO_GUIDANCE P0-8).

Global direction-separation constant chosen before the varying configuration.
Prevents an admissible sequence from weakening the geometric hypothesis by
sending its private `TubeFamily.sep` to zero.
-/
structure UniformSeparation (d : ℕ) where
  /-- Uniform lower bound on direction separation. -/
  sep_bound : ℝ
  sep_pos : 0 < sep_bound

/-- Separation compatibility (TODO_GUIDANCE P0-8).

A `TubeFamily` is compatible with the uniform separation bound if its
`sep` is at least `sep_bound`. This ensures the `sep * δ ≤ ‖dir t - dir t'‖`
hypothesis holds uniformly, not with a configuration-dependent `sep → 0`.
-/
def SepCompatible {n d : ℕ} (F : TubeFamily n d)
    (sepU : UniformSeparation d) : Prop :=
  sepU.sep_bound ≤ F.sep

/-- Combined uniform descent assumptions (TODO_GUIDANCE P0-1, P0-8).

Bundles the uniform certificates. Every constant herein is chosen
before the physical configuration is quantified, ensuring the top-level
uniform theorem cannot be proved by post-processing local constants.
-/
structure UniformDescentAssumptions (d : ℕ) where
  geom : UniformGeomInput d
  hard : UniformHardeningBudget d
  comp : UniformDescentComplexity d
  sepU : UniformSeparation d

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

/-- Bundled uniform scalar configuration (TODO_GUIDANCE P0-7).

Packages the label type `α` (with its instances) INSIDE the configuration,
so the uniform constant `C` in `UniformSubpowerLE` is chosen BEFORE `α`.
This removes the hidden dependence of `C` on the history alphabet `α`.

Previously, `scalar_closure_uniform {α : Type} ...` fixed `α` before the
`∃ C`, allowing `C` to depend on `α`. Now `α` is part of `cfg`, so `C`
must work for all `α` simultaneously.
-/
structure BundledUniformScalarConfig (d : ℕ) (δ : ℝ) where
  α : Type
  decα : DecidableEq α
  finα : Fintype α
  cfg : @UniformScalarConfig d α decα finα δ

attribute [instance] BundledUniformScalarConfig.decα BundledUniformScalarConfig.finα

/-- Subtree load bounded by shading volume (P0-4c).

For every retained node `x ∈ T`, tube `t`, and scale `δ'`,
the rerooted subtree's terminal tube load is bounded by the
full shading volume.

This is the compatibility condition that allows constructing the
restricted source `S_x` via `exists_subset_volume`. When `load` is
source-derived via `pathMass` (P1-9), this bound follows from the
fact that the subtree's packets are a subset of all packets.

Currently taken as a hypothesis (like `LedgerBudgetCompatible` and
`SepCompatible`); P1-9 will derive it from the source construction.
-/
def SubtreeLoadBounded {d : ℕ} {α : Type} [DecidableEq α] [Fintype α]
    {δ₀ : ℝ} (cfg : UniformScalarConfig d α δ₀) : Prop :=
  ∀ (x : List α) (_ : x ∈ cfg.T) (t : Fin cfg.phys.n) (δ' : ℝ),
    0 < δ' → δ' < 1 →
    termLoad (reroot cfg.T x)
      (fun s => cfg.termTube (x ++ s))
      (fun s δ'' => cfg.load (x ++ s) δ'')
      t δ' ≤
      (MeasureTheory.volume (cfg.phys.shading.Y t δ')).toReal

/-- Build an `AdmissibleGeomConfig` from subtree data (for P0-2 threading).

Given `cfg : UniformScalarConfig d α`, `x ∈ cfg.T`, and `δ`, constructs
the admissible geometric configuration.

NOTE (P0-4): Currently just reuses `cfg.phys`. The full version must
construct the RESTRICTED source `S_x` for the subtree at `x` (retained
node), with the rerooted terminal tube load equal to the shading load
of `S_x`. That construction is deferred to P0-4.

Paper reference: §10.1, eq (131)-(133). The paper defines for each vertex `a`
  `W_a(x) := ∑_{γ∈Desc(a)} u_γ(x)`  (132)
where `u_γ(x) = E_γ(ρ_γ 1_{Γ_k} f_{γ,I})(x)` is source-derived via conditional
expectations (131). The children partition gives (133): `W_a = ∑_{b} W_b`.
The restricted source `S_x` should have shading density proportional to `W_x`.

This requires P1-9 (build history loads from pathMass): the `load` field must
be proved source-derived (via `pathMass`/`u_γ`), not an arbitrary function.
Only then can the restricted shading `Y_x` be constructed with
`volume(Y_x t δ) = termLoad_x t δ`.
-/

-- Measure theory lemma for P0-4: intermediate value property for volume.
-- Given measurable S with (volume S).toReal = V and 0 ≤ v ≤ V,
-- there is a measurable S' ⊆ S with (volume S').toReal = v.
-- Proof: trivial cases v=0 (take ∅) and v=V (take S).
-- For 0 < v < V, use hyperplane slicing and IVT.
theorem exists_subset_volume {d : ℕ} (hd : 1 ≤ d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : MeasurableSet S)
    (V : ℝ) (hV : (MeasureTheory.volume S).toReal = V)
    (v : ℝ) (hv0 : 0 ≤ v) (hvV : v ≤ V) :
    ∃ S' : Set (EuclideanSpace ℝ (Fin d)),
      MeasurableSet S' ∧ S' ⊆ S ∧ (MeasureTheory.volume S').toReal = v := by
  rcases eq_or_ne v 0 with rfl | hne0
  · exact ⟨∅, MeasurableSet.empty, Set.empty_subset _, by simp⟩
  rcases eq_or_ne v V with rfl | hneV
  · exact ⟨S, hS, Set.Subset.rfl, hV⟩
  -- Now 0 < v < V
  have hvp : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hne0)
  have hvV' : v < V := lt_of_le_of_ne hvV hneV
  -- Now 0 < v < V and d ≥ 1 (hd). Use hyperplane slicing + IVT.
  -- Define f(t) = (volume (S ∩ {x | x k ≤ t})).toReal for k = ⟨0, hd⟩.
  -- f monotone, continuous (hyperplanes null via Fubini),
  -- lim atBot = 0, lim atTop = V. IVT gives t₀ with f(t₀) = v.
  -- Take S' = S ∩ {x | x k ≤ t₀}. Details deferred.
  sorry


-- NOTE: admGeomConfigOfSubtree is defined after restrictedShading (below),
-- since it uses the restricted shading to build S_x.

/-- Subtree terminal tube load (P0-4).

For `x ∈ cfg.T`, the rerooted subtree's load at tube `t` and scale `δ'` is
the sum of `cfg.load` over rerooted leaves mapping to `t` via the rerooted
`termTube`. This is the `termLoad` that the restricted source `S_x` must
realize as its shading volume.
-/
noncomputable def subtreeTermLoad {d : ℕ} {α : Type} [DecidableEq α] [Fintype α]
    {δ₀ : ℝ} (cfg : UniformScalarConfig d α δ₀) (x : List α)
    (t : Fin cfg.phys.n) (δ' : ℝ) : ℝ :=
  termLoad (reroot cfg.T x)
    (fun s => cfg.termTube (x ++ s))
    (fun s δ'' => cfg.load (x ++ s) δ'')
    t δ'

/-- Restricted shading for subtree `x` (P0-4b, in progress).

Given the bound `subtreeTermLoad ≤ shadeVol` (which follows from P1-9 when
`load` is source-derived), constructs a `Shading` whose volumes equal the
subtree's terminal tube loads, using `exists_subset_volume`.

The bound hypothesis is the precise gap: P1-9 must prove that the
source-derived `load` (via `pathMass`) satisfies
`termLoad_x t δ' ≤ shadeVol t δ'`.
-/

-- Restricted shading for subtree x (P0-4b).
-- Via exists_subset_volume: for each (t, δ'), pick Y_x(t,δ') ⊆ Y(t,δ')
-- with volume = subtreeTermLoad. Needs 0 ≤ termLoad (from termLoad_nonneg)
-- and termLoad ≤ shadeVol (hbound).
noncomputable def restrictedShading {d : ℕ} (hd : 1 ≤ d) {α : Type} [DecidableEq α] [Fintype α]
    {δ₀ : ℝ} (cfg : UniformScalarConfig d α δ₀) (x : List α) (hx : x ∈ cfg.T)
    (hbound : ∀ t δ', 0 < δ' → δ' < 1 →
      subtreeTermLoad cfg x t δ' ≤
        (MeasureTheory.volume (cfg.phys.shading.Y t δ')).toReal) :
    Shading cfg.phys.family := by
  -- For each (t, δ'), get the subset via exists_subset_volume
  -- Use choice to obtain the function
  have hchoice : ∀ t δ', 0 < δ' → δ' < 1 →
      ∃ S' : Set (EuclideanSpace ℝ (Fin d)),
        MeasurableSet S' ∧ S' ⊆ cfg.phys.shading.Y t δ' ∧
        (MeasureTheory.volume S').toReal = subtreeTermLoad cfg x t δ' := by
    intro t δ' hδ0 hδ1
    apply exists_subset_volume hd
    · exact cfg.phys.shading.measurable t δ' hδ0 hδ1
    · rfl
    · -- 0 ≤ subtreeTermLoad: via termLoad_nonneg
      unfold subtreeTermLoad
      apply termLoad_nonneg _ _ _ _ t δ' hδ0 hδ1
      -- Need: ∀ s ∈ treeLeaves (reroot cfg.T x), ∀ δ'', 0 < δ'' → δ'' < 1 →
      --   0 ≤ (fun s δ'' => cfg.load (x ++ s) δ'') s δ''
      intro s hs δ'' hδ0' hδ1'
      have hmem : x ++ s ∈ treeLeaves cfg.T :=
        reroot_leaf_lift cfg.T x hs
      exact cfg.hload (x ++ s) hmem δ'' hδ0' hδ1'
    · exact hbound t δ' hδ0 hδ1
  -- Use choice to get Y_x as a function
  choose Yx hYx_meas hYx_sub hYx_vol using hchoice
  -- Construct the Shading
  refine ⟨fun t δ' => if h : 0 < δ' ∧ δ' < 1 then Yx t δ' h.1 h.2 else ∅, ?_, ?_⟩
  · -- measurable
    intro t δ hδ0 hδ1
    have hcond : 0 < δ ∧ δ < 1 := ⟨hδ0, hδ1⟩
    rw [dif_pos hcond]
    exact hYx_meas t δ hδ0 hδ1
  · -- subset_tube: Y_x ⊆ Y ⊆ tube
    intro t δ hδ0 hδ1
    have hcond : 0 < δ ∧ δ < 1 := ⟨hδ0, hδ1⟩
    rw [dif_pos hcond]
    exact Set.Subset.trans (hYx_sub t δ hδ0 hδ1)
      (cfg.phys.shading.subset_tube t δ hδ0 hδ1)

/-- Restricted geometric config for subtree `x` (P0-4).

Builds the `AdmissibleGeomConfig` S_x using the restricted shading,
so that `S_x.shadeVol t δ' = subtreeTermLoad cfg x t δ'`.

Requires `hpos_x`: the restricted shading has positive union volume
(i.e., the subtree carries positive load). If the subtree has zero load,
the pair bound is trivial (0 ≤ ...).
-/
noncomputable def admGeomConfigOfSubtree {d : ℕ} (hd : 1 ≤ d) {α : Type} [DecidableEq α] [Fintype α]
    {δ₀ : ℝ} (cfg : UniformScalarConfig d α δ₀) (x : List α) (hx : x ∈ cfg.T)
    (hbound : SubtreeLoadBounded cfg)
    (hpos_x : ∀ δ', 0 < δ' → δ' < 1 →
      0 < (MeasureTheory.volume (⋃ t, (restrictedShading hd cfg x hx
        (fun t δ' h0 h1 => hbound x hx t δ' h0 h1)).Y t δ')).toReal)
    (δ : ℝ) (hδ0 : 0 < δ) :
    AdmissibleGeomConfig d δ where
  phys := ⟨cfg.phys.n, cfg.phys.family,
    restrictedShading hd cfg x hx (fun t δ' h0 h1 => hbound x hx t δ' h0 h1),
    hpos_x⟩

-- uninhabited issue by deriving the load from the source. The correct P0-4
-- construction builds a RESTRICTED physical source `S_x` for each subtree `x`,
-- with `S_x.shadeVol = termLoad` of the re-rooted subtree. That construction
-- is deferred.

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
theorem scalar_closure_uniform {d : ℕ}
    (hU : UniformDescentAssumptions d)
    -- P0-6: local ledgers must respect the uniform hardening budget.
    -- Without this, a config with huge `card K` or tiny `c₀` could break uniformity.
    -- P0-7: α is now inside the bundled config, so C cannot depend on it.
    (hcompat : ∀ δ : ℝ, ∀ cfg : BundledUniformScalarConfig d δ,
      LedgerBudgetCompatible cfg.cfg.L hU.hard)
    -- P0-8: direction separation must respect the uniform bound.
    -- Without this, a config could send its private `sep` to zero.
    (hsepcompat : ∀ δ : ℝ, ∀ cfg : BundledUniformScalarConfig d δ,
      SepCompatible cfg.cfg.phys.family hU.sepU)
    -- P0-4c: subtree loads bounded by shading volumes.
    -- Enables restricted source construction via exists_subset_volume.
    (hloadbound : ∀ δ : ℝ, ∀ cfg : BundledUniformScalarConfig d δ,
      SubtreeLoadBounded cfg.cfg) :
    UniformSubpowerLE (BundledUniformScalarConfig d)
      (fun δ cfg => ∑ t : Fin cfg.cfg.phys.n,
        (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).shadeVol t δ)
      (fun δ cfg =>
        (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ) := by
  intro ε hε
  -- By the uniform assumptions, obtain uniform constants BEFORE the config.
  obtain ⟨C_geom, hC_geom, hgeom⟩ := hU.geom ε hε
  -- Combine uniform constants. The complexity certificate (hU.comp) will
  -- eventually provide subpower control on tree complexity (P0-2 new);
  -- for now, the constant uses the geometric and hardening bounds.
  -- The full threading through the descent machinery is deferred.
  refine ⟨C_geom * (hU.hard.hcard_bound + 1), ?_, fun δ hδ0 hδ1 cfg => ?_⟩
  · apply mul_nonneg hC_geom
    linarith [hU.hard.hcard_nonneg]
  · -- For each config, apply the local descent with UNIFORM constants.
    -- hU.geom : uniform pair bound (via uniformGeomPair_to_local);
    -- hU.hard : uniform ledger bounds;
    -- hU.comp : uniform subpower complexity (P0-2 new, to be formalized).
    -- The full threading through scalar_closure_discharged_physical
    -- is deferred (TODO_GUIDANCE P0-5).
    --
    -- P0-5 PROGRESS: Instantiate the uniform geometric input at the
    -- config's physical data. Define the AdmissibleGeomConfig from
    -- cfg.cfg.phys and apply hgeom to get the pair energy bound.
    -- The remaining descent (via descent_bound, faithful_gate_discharged,
    -- node_hardening_subpower) is deferred.
    let cfg' : AdmissibleGeomConfig d δ := ⟨cfg.cfg.phys⟩
    have hpair := hgeom δ hδ0 hδ1 cfg'
    -- hpair : pairEnergy d δ cfg' ≤ C_geom * δ ^ (-ε) * geomRHS d δ cfg'
    --
    -- P0-5b: Apply scalar_closure_discharged_physical with the uniform data.
    -- The geom_pair hypothesis (per-subtree pair bound) is derived from
    -- hU.geom via the P0-4 restricted source construction.
    -- Currently marked sorry: needs the full P0-4 wiring.
    have hgeom_pair : ∀ x ∈ cfg.cfg.T, SubpowerLE
        (fun δ => ∑ t : Fin cfg.cfg.phys.n, ∑ t' : Fin cfg.cfg.phys.n,
          if t ≠ t' then termLoad (reroot cfg.cfg.T x) (fun s => cfg.cfg.termTube (x ++ s))
            (fun s δ => cfg.cfg.load (x ++ s) δ) t δ
            * termLoad (reroot cfg.cfg.T x) (fun s => cfg.cfg.termTube (x ++ s))
            (fun s δ => cfg.cfg.load (x ++ s) δ) t' δ
          else 0)
        (fun δ => (physicalRealization cfg.cfg.phys.family cfg.cfg.phys.shading cfg.cfg.phys.hpos).unionVol δ *
          totalLoad (reroot cfg.cfg.T x) (fun s δ => cfg.cfg.load (x ++ s) δ) δ) := by
      -- For each x, build restricted S_x via P0-4, apply hU.geom,
      -- and use unionVol_{S_x} ≤ unionVol_orig.
      -- Deferred: needs restrictedShading to be more than a sorry.
      sorry
    -- Apply the physical scalar closure with uniform-derived geom_pair.
    -- The constant from scalar_closure_discharged_physical depends on the
    -- config; we need to show it's bounded uniformly via hU.hard.
    -- Deferred: uniform constant tracking.
    sorry

end FilteredDescent
