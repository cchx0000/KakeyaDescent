import Definitions.Def_FilteredDescent_Analytic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Filtered descent — physical δ-tubes (paper's standing geometric assumptions)

This file grounds the abstract analytic interface `FilteredDescent.ShadedTubes`
(see `Definitions/Def_FilteredDescent_Analytic.lean`) in real geometry:
physical δ-tubes in `ℝ^d = EuclideanSpace ℝ (Fin d)` with Lebesgue measure
`volume`.

* A **physical δ-tube** (`TubeFamily.tube`) is the closed δ-neighborhood of a
  unit line segment `{ c + s • v | s ∈ [0,1] }`, with center `c` and unit
  direction `v`.
* A **tube family** (`TubeFamily`) is a finite family of such tubes indexed by
  `Fin n`, with **direction separation** `‖v t - v t'‖ ≥ sep * δ` for `t ≠ t'`
  and a fixed constant `sep > 0`.  This is the formal counterpart of the
  paper's standing assumption that the tube family is direction-separated at
  scale δ — the geometric hypothesis underlying the Kakeya-type inputs
  (H2)/(H3)/(H4).
* A **shading** (`Shading`) at scale δ is, for each tube `t`, a measurable
  portion `Y t δ ⊆ tube t δ` (`MeasurableSet`) — the paper's shaded sets
  `Y(T)`.  The shading is stated per scale: a δ-independent shading would
  have to sit inside `⋂_{δ>0} tube t δ`, i.e. inside the bare segment, so it
  could not carry positive volume.

The **realization theorem** (`physicalRealization`) builds a
`FilteredDescent.ShadedTubes n` from this data, with
`shadeVol t δ = (volume (Y t δ)).toReal`,
`unionVol δ = (volume (⋃ t, Y t δ)).toReal`, and
`multiplicity δ = (∑ t, shadeVol t δ) / unionVol δ`.
The geometric content is real, not assumed:
nonnegativity from `measure_nonneg`;
`shade_le_union` from `Y t δ ⊆ ⋃ t, Y t δ` via `measure_mono`;
`mult_eq` from `div_mul_cancel₀` using `0 < unionVol δ`;
`mult_pos` from the union bound `volume (⋃ t, Y t δ) ≤ ∑ t, volume (Y t δ)`.
Finiteness of every volume is *derived*: each tube is compact (hence of
finite volume), and each shading sits inside its tube.

What this model does NOT capture (honest scoping):
* No sticky / marked structure: there is no history tree, no sticky lines,
  and no markings.  The descent's combinatorial side
  (`Def_FilteredDescent_Tree.lean`) is not wired to these tubes.
* No multi-scale structure: shadings are stated one scale at a time.
* Direction separation is *assumed* as the paper's standing hypothesis; it
  is not needed for the realization of the interface itself (it is the input
  to the Kakeya-type estimates (H2)/(H3)/(H4), which are not proved here).
  Likewise `dir_unit` and the `MeasurableSet` field of a shading are model
  data: the realization proof only needs monotonicity and finiteness of
  `volume`, which hold for outer measures in general.
-/

namespace FilteredDescent

open MeasureTheory
open scoped ENNReal

variable {n d : ℕ}

/-- Finite direction-separated tube family: the paper's standing geometric
assumption on the tube family underlying the Kakeya-type inputs.  Centers
`center`, unit directions `dir`, and a separation constant `sep > 0` with
`‖dir t - dir t'‖ ≥ sep * δ` for `t ≠ t'` at scale `δ ∈ (0,1)` — the formal
counterpart of the paper's δ-separated direction set. -/
structure TubeFamily (n d : ℕ) where
  center : Fin n → EuclideanSpace ℝ (Fin d)
  dir : Fin n → EuclideanSpace ℝ (Fin d)
  dir_unit : ∀ t, ‖dir t‖ = 1
  sep : ℝ
  sep_pos : 0 < sep
  dir_separated : ∀ t t' : Fin n, t ≠ t' → ∀ δ : ℝ, 0 < δ → δ < 1 →
    sep * δ ≤ ‖dir t - dir t'‖

/-- The physical δ-tube of tube `t`: the closed δ-neighborhood of the unit
segment `{ center t + s • dir t | s ∈ [0,1] }`. -/
def TubeFamily.tube (F : TubeFamily n d) (t : Fin n) (δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  { x | ∃ s : ℝ, s ∈ Set.Icc 0 1 ∧ dist x (F.center t + s • F.dir t) ≤ δ }

/-- A δ-tube is the continuous image of the compact box
`[0,1] ×ˢ closedBall 0 δ`, hence compact. -/
theorem TubeFamily.isCompact_tube (F : TubeFamily n d) (t : Fin n) (δ : ℝ) :
    IsCompact (F.tube t δ) := by
  have heq : F.tube t δ =
      (fun p : ℝ × EuclideanSpace ℝ (Fin d) => F.center t + p.1 • F.dir t + p.2) ''
        (Set.Icc 0 1 ×ˢ Metric.closedBall 0 δ) := by
    ext x
    constructor
    · rintro ⟨s, hs, hdist⟩
      refine ⟨(s, x - (F.center t + s • F.dir t)), ⟨hs, ?_⟩, ?_⟩
      · show x - (F.center t + s • F.dir t) ∈ Metric.closedBall 0 δ
        rw [Metric.mem_closedBall, dist_zero_right]
        rw [dist_eq_norm] at hdist
        exact hdist
      · show F.center t + s • F.dir t + (x - (F.center t + s • F.dir t)) = x
        abel
    · rintro ⟨⟨s, w⟩, ⟨hs, hw⟩, rfl⟩
      refine ⟨s, hs, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      have h : dist (F.center t + s • F.dir t + w) (F.center t + s • F.dir t)
          = ‖w‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      rw [h]
      exact hw
  rw [heq]
  exact (isCompact_Icc.prod (isCompact_closedBall 0 δ)).image
    ((continuous_const.add (continuous_fst.smul continuous_const)).add continuous_snd)

/-- A δ-tube has finite volume (it is compact; `volume` on `ℝ^d` is finite
on compacts). -/
theorem TubeFamily.tube_volume_lt_top (F : TubeFamily n d) (t : Fin n) (δ : ℝ) :
    volume (F.tube t δ) < ∞ :=
  (F.isCompact_tube t δ).measure_lt_top

/-- A shading of a tube family: for each tube `t` and scale `δ`, a measurable
portion `Y t δ` of the δ-tube — the paper's shaded sets `Y(T)`. -/
structure Shading (F : TubeFamily n d) where
  Y : Fin n → ℝ → Set (EuclideanSpace ℝ (Fin d))
  measurable : ∀ t δ, 0 < δ → δ < 1 → MeasurableSet (Y t δ)
  subset_tube : ∀ t δ, 0 < δ → δ < 1 → Y t δ ⊆ F.tube t δ

/-- Scale-indexed physical configuration (TODO_GUIDANCE P0-2).

For Kakeya finite-scale asymptotics, the tube family changes with `δ` and
its cardinality may grow like a power of `δ^{-1}`. This bundles the
`δ`-dependent `n`, family, and shading; the realized `ShadedTubes` is
derived via `physicalRealization`.

The final scalar theorem quantifies over the configuration *after* choosing
the uniform constant (see `UniformSubpowerLE`). -/
structure PhysicalConfig (d : ℕ) (δ : ℝ) where
  n : ℕ
  family : TubeFamily n d
  shading : Shading family
  hpos : ∀ δ', 0 < δ' → δ' < 1 → 0 < (volume (⋃ t, shading.Y t δ')).toReal

/-- Realization: a direction-separated physical tube family with measurable
shadings realizes the abstract `ShadedTubes` analytic interface, with
`shadeVol t δ = (volume (Y t δ)).toReal`,
`unionVol δ = (volume (⋃ t, Y t δ)).toReal`, and
`multiplicity δ = (∑ t, shadeVol t δ) / unionVol δ`.

The only analytic hypotheses are the positivity of the union volume
(needed for `mult_pos` and `mult_eq`); finiteness of all volumes is derived
from the tube geometry. -/
noncomputable def physicalRealization (F : TubeFamily n d) (S : Shading F)
    (hpos : ∀ δ, 0 < δ → δ < 1 → 0 < (volume (⋃ t, S.Y t δ)).toReal) :
    ShadedTubes n := by
  have hfin : ∀ t δ, 0 < δ → δ < 1 → volume (S.Y t δ) ≠ ∞ := by
    intro t δ h0 h1
    exact ne_top_of_le_ne_top (F.tube_volume_lt_top t δ).ne
      (measure_mono (S.subset_tube t δ h0 h1))
  have hUfin : ∀ δ, 0 < δ → δ < 1 → volume (⋃ t, S.Y t δ) ≠ ∞ := by
    intro δ h0 h1
    have hsumfin : ∑ t, volume (F.tube t δ) ≠ ∞ :=
      ENNReal.sum_ne_top.mpr (fun t _ => (F.tube_volume_lt_top t δ).ne)
    refine ne_top_of_le_ne_top hsumfin ?_
    calc volume (⋃ t, S.Y t δ) ≤ ∑ t, volume (S.Y t δ) :=
            measure_iUnion_fintype_le volume _
        _ ≤ ∑ t, volume (F.tube t δ) :=
            Finset.sum_le_sum (fun t _ => measure_mono (S.subset_tube t δ h0 h1))
  refine ShadedTubes.mk (fun t δ => (volume (S.Y t δ)).toReal)
    (fun δ => (volume (⋃ t, S.Y t δ)).toReal)
    (fun δ => (∑ t, (volume (S.Y t δ)).toReal) / (volume (⋃ t, S.Y t δ)).toReal)
    (fun _ _ _ _ => ENNReal.toReal_nonneg)
    (fun _ _ _ => ENNReal.toReal_nonneg) ?_ ?_ ?_
  · intro δ h0 h1
    show 0 < (∑ t, (volume (S.Y t δ)).toReal) / (volume (⋃ t, S.Y t δ)).toReal
    refine div_pos ?_ (hpos δ h0 h1)
    have hsumfin : ∑ t, volume (S.Y t δ) ≠ ∞ :=
      ENNReal.sum_ne_top.mpr (fun t _ => hfin t δ h0 h1)
    have hle : (volume (⋃ t, S.Y t δ)).toReal ≤ (∑ t, volume (S.Y t δ)).toReal :=
      (ENNReal.toReal_le_toReal (hUfin δ h0 h1) hsumfin).mpr
        (measure_iUnion_fintype_le volume _)
    rw [ENNReal.toReal_sum (fun t _ => hfin t δ h0 h1)] at hle
    exact lt_of_lt_of_le (hpos δ h0 h1) hle
  · intro δ h0 h1
    show (∑ t, (volume (S.Y t δ)).toReal) / (volume (⋃ t, S.Y t δ)).toReal *
        (volume (⋃ t, S.Y t δ)).toReal = ∑ t, (volume (S.Y t δ)).toReal
    exact div_mul_cancel₀ _ (ne_of_gt (hpos δ h0 h1))
  · intro t δ h0 h1
    show (volume (S.Y t δ)).toReal ≤ (volume (⋃ t, S.Y t δ)).toReal
    exact (ENNReal.toReal_le_toReal (hfin t δ h0 h1) (hUfin δ h0 h1)).mpr
      (measure_mono (Set.subset_iUnion (fun t => S.Y t δ) t))

/-- The realized abstract shading interface for a physical configuration. -/
noncomputable def PhysicalConfig.realized {d : ℕ} {δ : ℝ}
    (cfg : PhysicalConfig d δ) : ShadedTubes cfg.n :=
  physicalRealization cfg.family cfg.shading cfg.hpos


end FilteredDescent
