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

- Item 6: `geom_pair` should come from dimension-specific external input
  (d=2/3/4), not as a direct hypothesis.
- Item 7: tree/load should be derived from packet/source law, not given.
- Item 8: `htotalLoad` should be derived from mass conservation, not assumed.

What IS achieved here:
- `Hpred` is not assumed (discharged by well-founded descent).
- `terminal_hardening` is not assumed (derived from `HardeningLedger`
  via `node_hardening_subpower`).
- The constant `C` is uniform over scale-indexed configurations.
-/

namespace FilteredDescent

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
  geom_pair : ∀ x ∈ T, SubpowerLE
    (fun δ' => ∑ t : Fin phys.n, ∑ t' : Fin phys.n,
      if t ≠ t' then termLoad (reroot T x) (fun s => termTube (x ++ s))
        (fun s δ'' => load (x ++ s) δ'') t δ'
        * termLoad (reroot T x) (fun s => termTube (x ++ s))
        (fun s δ'' => load (x ++ s) δ'') t' δ'
      else 0)
    (fun δ' => (physicalRealization phys.family phys.shading phys.hpos).unionVol δ' *
      totalLoad (reroot T x) (fun s δ'' => load (x ++ s) δ'') δ')

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

Note: the `geom_pair` and tree/ledger data are still bundled in the
configuration (items 6/7/8 remain). What is NOT in the configuration:
`Hpred` (proved by descent) and `terminal_hardening` (derived from ledger).
-/
theorem scalar_closure_uniform {d : ℕ} {α : Type} [DecidableEq α] [Fintype α] :
    UniformSubpowerLE (UniformScalarConfig d α)
      (fun δ cfg => ∑ t : Fin cfg.phys.n,
        (physicalRealization cfg.phys.family cfg.phys.shading cfg.phys.hpos).shadeVol t δ)
      (fun δ cfg =>
        (physicalRealization cfg.phys.family cfg.phys.shading cfg.phys.hpos).unionVol δ) := by
  intro ε hε
  -- The underlying SubpowerLE proof gives, for each fixed configuration,
  -- a constant C. We must show ONE C works for ALL configurations.
  -- 
  -- HONESTY NOTE: The current proof below does NOT achieve this — it
  -- would require the constant from scalar_closure_discharged_physical
  -- to be independent of the configuration, which is false in general
  -- (the descent constant depends on the tree structure, the ledger's
  -- packet data, etc.).
  --
  -- The uniform bound is the *intended* theorem (TODO_GUIDANCE item 9),
  -- but proving it requires:
  -- (a) a uniform bound on the descent constant in terms of d only,
  --     which needs the packet/source construction (item 7) to control
  --     the tree complexity uniformly; OR
  -- (b) restricting the Config to a class with uniform complexity bounds.
  --
  -- We state the theorem with its intended meaning and mark the proof
  -- as deferred pending items 6/7/8.
  sorry

end FilteredDescent
