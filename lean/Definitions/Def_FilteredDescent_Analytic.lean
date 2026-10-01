import Definitions.Def_FilteredDescent_Subpower
import Definitions.Def_FilteredDescent_Tree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Filtered descent — analytic interface (paper (53), (81), (142), (177))

The analytic side of the formalization: the subpower notation, the finite
shaded tube family, and the imported Kakeya-type estimates.  All
quantitative data are functions of the scale `δ ∈ (0,1)`; the deep
analytic inputs are stated as explicit hypotheses:

* (H2) `PlanarInput`: the hereditary planar Córdoba cutoff is subpower
  (paper (53), from Córdoba [2]).
* (H3) `StickyInput`: the sticky Kakeya union + multiplicity bounds
  (paper (177), from [7] Wang–Zahl and [10] the sticky/non-sticky
  reduction).
* (H4) `Marked4DInput`: the uniform marked 4D sticky input
  (paper (81), from [9], the unpublished companion manuscript).

(H3) and (H4) have the same abstract quantitative shape (a union lower
bound plus a multiplicity upper bound, up to subpower losses): that shape
is the interface the descent consumes.  They are *different assumptions*:
(H3) is the sticky estimate for `d = 3` from [7,10], (H4) the marked
estimate for `d = 4` from [9], applied to different geometric families.
At use sites (`root_cross_gate`, `scalar_closure`) the dimension
hypothesis selects exactly one of them, so the two are never
interchangeable there.

`GateStage` bundles one descent stage — the history tree together with
the shaded tube family it is built over (tubes indexed by `Fin n`,
shared) — for the root-cross gate (M7).  The paper's assembly deriving
the geometric pair bound from the per-dimension input is the proof
obligation of the gate theorem.
-/

namespace FilteredDescent

/-- (H2) Hereditary planar Córdoba input (paper (53), from [2]):
the planar cutoff `Kpr = L_σ / (τ * λ)` is subpower in `δ`, uniformly
for `δ ∈ (0,1)`. -/
def PlanarInput (Kpr : ℝ → ℝ) : Prop :=
  SubpowerLE Kpr (fun _ => 1)

/-- (H3) Sticky Kakeya input (paper (177), from [7] and [10]):
multiplicity upper bound + geometric pair-incidence estimate, up to
subpower losses uniform for `δ ∈ (0,1)`.

The pair-incidence bound controls `∑_{t≠t'} |Y(t)|·|Y(t')|` by
`|⋃ Y| · ∑ |Y(t)|`.  This is a *geometric* estimate on the tube family;
the final union lower bound (paper (214)) is *derived* from it via the
filtered descent (`root_cross_gate` + `terminal_incidence_count`), not
assumed. -/
def StickyInput {n : ℕ} (shadeVol : Fin n → ℝ → ℝ) (unionVol
    multiplicity : ℝ → ℝ) : Prop :=
  SubpowerLE multiplicity (fun _ => 1) ∧
  SubpowerLE (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
      if t ≠ t' then shadeVol t δ * shadeVol t' δ else 0)
    (fun δ => unionVol δ * ∑ t, shadeVol t δ)

/-- (H4) Uniform marked 4D sticky input (paper (81), from [9], unpublished
companion manuscript).  It has the same abstract quantitative shape as
(H3) — multiplicity upper bound + geometric pair-incidence estimate —
because that shape is what the descent consumes; it is a *separate*
assumption (the marked `d = 4` estimate, uniform over marks), selected by
the `d = 4` hypothesis at use sites.  As with (H3), the union lower bound
is derived via the descent, not assumed. -/
def Marked4DInput {n : ℕ} (shadeVol : Fin n → ℝ → ℝ) (unionVol
    multiplicity : ℝ → ℝ) : Prop :=
  SubpowerLE multiplicity (fun _ => 1) ∧
  SubpowerLE (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
      if t ≠ t' then shadeVol t δ * shadeVol t' δ else 0)
    (fun δ => unionVol δ * ∑ t, shadeVol t δ)

/-- Finite shaded tube family at scale `δ`: the analytic interface for
the terminal incidence count (paper (214)).  `shadeVol t δ = |Y(t)|` is
the shading volume, `unionVol δ = |⋃_t Y(t)|`, and `multiplicity δ` is the
average overlap `Σ_t |Y(t)| / |⋃_t Y(t)|`, all as functions of `δ ∈ (0,1)`. -/
structure ShadedTubes (n : ℕ) where
  shadeVol : Fin n → ℝ → ℝ
  unionVol : ℝ → ℝ
  multiplicity : ℝ → ℝ
  shade_nonneg : ∀ t δ, 0 < δ → δ < 1 → 0 ≤ shadeVol t δ
  union_nonneg : ∀ δ, 0 < δ → δ < 1 → 0 ≤ unionVol δ
  mult_pos : ∀ δ, 0 < δ → δ < 1 → 0 < multiplicity δ
  mult_eq : ∀ δ, 0 < δ → δ < 1 → multiplicity δ * unionVol δ = ∑ t, shadeVol t δ

/-- One descent stage for the root-cross gate (paper (142)): the history
tree together with the shaded tube family it is built over.  The tube
index type `Fin n` is shared: `termTube` sends each history to its
terminal tube, and `shadeVol`/`unionVol`/`multiplicity` are the analytic
data of the same tube family.  Quantitative fields are functions of the
scale `δ ∈ (0,1)`; the tree, the tube/carrier labelings are `δ`-free.
This bundling is the formal counterpart of the paper's standing
assumption that the tree and the tube family belong to one physical
descent stage. -/
structure GateStage (α : Type) [DecidableEq α] (n m : ℕ) where
  tree : Finset (List α)
  hroot : [] ∈ tree
  hprefix : ∀ l ∈ tree, ∀ p : List α, p <+: l → p ∈ tree
  load : List α → ℝ → ℝ
  hload : ∀ γ ∈ treeLeaves tree, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ
  termTube : List α → Fin n
  carrier : List α → Fin m
  shadeVol : Fin n → ℝ → ℝ
  unionVol : ℝ → ℝ
  multiplicity : ℝ → ℝ
  shade_nonneg : ∀ t δ, 0 < δ → δ < 1 → 0 ≤ shadeVol t δ
  union_nonneg : ∀ δ, 0 < δ → δ < 1 → 0 ≤ unionVol δ
  mult_pos : ∀ δ, 0 < δ → δ < 1 → 0 < multiplicity δ
  mult_eq : ∀ δ, 0 < δ → δ < 1 → multiplicity δ * unionVol δ = ∑ t, shadeVol t δ
  Bpred : ℝ → ℝ
  Bpred_nonneg : ∀ δ, 0 < δ → δ < 1 → 0 ≤ Bpred δ
  /-- Bridge: the load on a tree leaf is bounded by the shading of its
  terminal tube.  This connects the tree-side data (`load`, `termTube`)
  to the analytic-side data (`shadeVol`). -/
  load_le_shade : ∀ γ ∈ treeLeaves tree, ∀ δ : ℝ, 0 < δ → δ < 1 →
    load γ δ ≤ shadeVol (termTube γ) δ

end FilteredDescent
