import Theorems.Thm_FilteredDescent_DescentInduction
import Definitions.Def_FilteredDescent_PhysicalTubes
import Mathlib.Data.Real.Basic

/-!
# End-to-end scalar closure with `Hpred` discharged (paper §13.2, (214))

This file composes Stream D (well-founded descent induction) with Stream E
(scalar closure via the faithful gate):

* Stream D's `faithful_gate_discharged` gives the faithful gate (141)+(142),
  `N(δ)² ≲ B^pred(δ) · N(δ)`, with the predecessor invariance `Hpred` (138)
  *proved* by well-founded induction on the descent labels — no longer a
  hypothesis;
* Stream E's bridge/divide argument (`htotalLoad`, then (142) → (214) by
  dividing by `N(δ)`) turns the gate output into the scalar incidence
  `∑_T |Y(T)| ≲ |⋃_T Y(T)|`.

The result, `scalar_closure_discharged`, is the strongest HONEST
`Hpred`-free scalar bound currently available: every remaining hypothesis
is named precisely below.  The old `scalar_closure`
(`Thm_FilteredDescent_ScalarClosure.lean`) is still true and untouched, but
is superseded by this faithful path.

## Named remaining hypotheses (NOT proved here)

1. `DescentLabels T lab` — the §§6–9 history-tree construction (support
   faces, confluence type `χ`, Cartan height) with the label-decrease
   property (135).  Named interface; the construction itself is not built.
2. `leaf_bound` — the pointwise leaf estimate, paper (53) at the minimal
   label `(2, 0, 0)`.  Named.
3. `terminal_hardening : ∀ x ∈ T, …` — the R5 terminal bound (148) on every
   re-rooted subtree.  Named per-subtree.  What the two streams prove:
   the R5 stream (`Thm_FilteredDescent_TerminalHardening.lean`) proves the
   ROOT instance from the `(θ,j,c)` common-source model data plus the
   *pointwise* `Hpred` (Stream E's wired path).  Two things are missing
   for a fully constructed version:
   (a) the `(θ,j,c)` data in `DescentData` is stated at the ROOT only
       (`cls` is indexed by `Fin (treeChildren T []).card`); re-running
       the common-source disintegration on each re-rooted subtree is
       genuine new mathematics, not a restriction argument;
   (b) with `Hpred` now in *subpower* form, the root wiring itself needs
       re-proving: the R5 aggregation's `h149` step
       (`D_T ≤ F_T · B^pred`) must be redone with the uniform-constant
       bound `Db ≤ C·δ^{-η}·B^pred` (the `uniform_proper_const` trick),
       and `hquant` pins `Bpred` from *below*, so a naive "`Bpred'`"
       substitution fails — the re-proof must re-run the R5 finale with
       the absorbed constant, fused into the well-founded descent (doing
       it afterwards would be circular, since the descent needs the root
       terminal bound and the root terminal bound needs the descent's
       subpower output at the root's children).
4. `geom_pair : ∀ x ∈ T, …` — the geometric pair estimate
   ((53)/(177)/(81) shape) on every re-rooted subtree.  Named per-subtree;
   the root instance is proved from `PlanarInput`/`StickyInput`/
   `Marked4DInput` by Stream E's `faithful_geom_pair`; the subtree
   versions need the pair estimate re-run per subtree.
5. `htotalLoad` — the combined (136)+(145) bridge identifying the total
   tree load with the tube-family shading sum.  Part of the §§6–9 data.
   (The finer per-tube bridge `termLoad = shadeVol` is not needed: the
   gate output only involves `totalLoad`, so it is not taken — no
   decorative hypotheses.)

Deliberately NOT in the interface: the `(θ,j,c)` model data and the
pointwise `Hpred` (both root-only, superseded by (3) above), `hnonroot`
(not needed by the discharged gate), and the retained-fraction `lamIn`
machinery of the old `(130)` detour (not needed once the faithful gate
supplies (142) itself).
-/

namespace FilteredDescent

open MeasureTheory

/-- Scalar filtered-descent closure (paper §13.2, (214)) with `Hpred`
discharged.

From the descent data: Stream D's `faithful_gate_discharged` gives
`N(δ)² ≲ B^pred(δ) · N(δ)` with `B^pred = S.unionVol` and with `Hpred`
(138) proved by the well-founded descent induction; the bridges identify
the tree load `N(δ)` with the tube-family shading sum; dividing by `N(δ)`
(zero case by nonnegativity) yields
`∑_T |Y(T)| ≲ |⋃_T Y(T)|`.

Every hypothesis is consumed; the remaining named inputs are (1)–(5) in
the module docstring. -/
theorem scalar_closure_discharged {n : ℕ} (S : ShadedTubes n)
    (T : Finset (List (Fin n))) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List (Fin n), p <+: l → p ∈ T)
    (lab : List (Fin n) → ℕ × ℕ × ℕ) (hlab : DescentLabels T lab)
    (termTube : List (Fin n) → Fin n) (load : List (Fin n) → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (htotalLoad : ∀ δ, totalLoad T load δ = ∑ t, S.shadeVol t δ)
    (leaf_bound : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 →
      load γ δ ≤ S.unionVol δ)
    (terminal_hardening : ∀ x ∈ T, SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad (reroot T x) (fun s => termTube (x ++ s))
        (fun s δ => load (x ++ s) δ) t δ) ^ 2)
      (fun δ => S.unionVol δ * totalLoad (reroot T x)
        (fun s δ => load (x ++ s) δ) δ))
    (geom_pair : ∀ x ∈ T, SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t δ
          * termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t' δ
        else 0)
      (fun δ => S.unionVol δ * totalLoad (reroot T x)
        (fun s δ => load (x ++ s) δ) δ)) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol := by
  -- The faithful gate (141)+(142) with `Hpred` discharged by Stream D:
  -- `N(δ)² ≲ B^pred(δ) · N(δ)` with `B^pred = S.unionVol`.
  have hNL : SubpowerLE (fun δ => (totalLoad T load δ) ^ 2)
      (fun δ => S.unionVol δ * totalLoad T load δ) :=
    faithful_gate_discharged T hroot hprefix lab hlab termTube load hload
      S.unionVol (fun δ hδ0 hδ1 => S.union_nonneg δ hδ0 hδ1)
      terminal_hardening geom_pair leaf_bound
  -- Bridges (faithful §10, (136)/(145)): tree load = tube-family shading.
  have hNL' : SubpowerLE (fun δ => (∑ t, S.shadeVol t δ) ^ 2)
      (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ) := by
    have e1 : (fun δ => (totalLoad T load δ) ^ 2)
        = (fun δ => (∑ t, S.shadeVol t δ) ^ 2) := by
      funext δ; rw [htotalLoad δ]
    have e2 : (fun δ => S.unionVol δ * totalLoad T load δ)
        = (fun δ => S.unionVol δ * ∑ t, S.shadeVol t δ) := by
      funext δ; rw [htotalLoad δ]
    rw [e1, e2] at hNL
    exact hNL
  -- Paper (142) → (214): divide `N(δ)² ≲ B^pred(δ) · N(δ)` by `N(δ)`.
  intro ε hε
  obtain ⟨C, hC, hCbound⟩ := hNL' ε hε
  refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
  show (∑ t, S.shadeVol t δ) ≤ C * δ ^ (-ε) * S.unionVol δ
  have hbd := hCbound δ hδ0 hδ1
  simp only [] at hbd
  by_cases hS : (∑ t, S.shadeVol t δ) = 0
  · -- Zero case: `0 ≤ C · δ^(-ε) · U` by nonnegativity.
    rw [hS]
    exact mul_nonneg (mul_nonneg hC (le_of_lt (Real.rpow_pos_of_pos hδ0 _)))
      (S.union_nonneg δ hδ0 hδ1)
  · -- Positive case: cancel the positive factor `∑ t, shadeVol t δ`.
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

/-- The physical loop, `Hpred`-free: the discharged scalar closure applied
to the real physical tube model (`physicalRealization`, Lebesgue-measurable
shading).  The abstract `ShadedTubes` interface is discharged by genuine
geometry; the predecessor invariance is discharged by the descent. -/
theorem scalar_closure_discharged_physical {n d : ℕ}
    (fam : TubeFamily n d) (sh : Shading fam)
    (hpos : ∀ δ, 0 < δ → δ < 1 → 0 < (volume (⋃ t, sh.Y t δ)).toReal)
    (T : Finset (List (Fin n))) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List (Fin n), p <+: l → p ∈ T)
    (lab : List (Fin n) → ℕ × ℕ × ℕ) (hlab : DescentLabels T lab)
    (termTube : List (Fin n) → Fin n) (load : List (Fin n) → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (htotalLoad : ∀ δ, totalLoad T load δ =
      ∑ t, (physicalRealization fam sh hpos).shadeVol t δ)
    (leaf_bound : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 →
      load γ δ ≤ (physicalRealization fam sh hpos).unionVol δ)
    (terminal_hardening : ∀ x ∈ T, SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad (reroot T x) (fun s => termTube (x ++ s))
        (fun s δ => load (x ++ s) δ) t δ) ^ 2)
      (fun δ => (physicalRealization fam sh hpos).unionVol δ * totalLoad (reroot T x)
        (fun s δ => load (x ++ s) δ) δ))
    (geom_pair : ∀ x ∈ T, SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t δ
          * termLoad (reroot T x) (fun s => termTube (x ++ s))
          (fun s δ => load (x ++ s) δ) t' δ
        else 0)
      (fun δ => (physicalRealization fam sh hpos).unionVol δ * totalLoad (reroot T x)
        (fun s δ => load (x ++ s) δ) δ)) :
    SubpowerLE (fun δ => ∑ t, (physicalRealization fam sh hpos).shadeVol t δ)
      (physicalRealization fam sh hpos).unionVol :=
  scalar_closure_discharged (physicalRealization fam sh hpos) T hroot hprefix
    lab hlab termTube load hload htotalLoad leaf_bound
    terminal_hardening geom_pair

end FilteredDescent
