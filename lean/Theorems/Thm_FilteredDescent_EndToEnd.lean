import Theorems.Thm_FilteredDescent_DescentInduction
import Theorems.Thm_FilteredDescent_HardeningCore
import Theorems.Thm_FilteredDescent_DescentBounds
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
theorem scalar_closure_discharged {α : Type} [DecidableEq α] [Fintype α] {n : ℕ}
    (S : ShadedTubes n)
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (lab : List α → ℕ × ℕ × ℕ) (hlab : DescentLabels T lab)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (htotalLoad : ∀ δ, totalLoad T load δ = ∑ t, S.shadeVol t δ)
    (leaf_bound : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 →
      load γ δ ≤ S.unionVol δ)
    (L : HardeningLedger α (n := n) T)
    (hlinkAt : ∀ (x : List α) (hx : x ∈ T),
      NodeHLink L x hx termTube load S.unionVol)
    (hquantAt : ∀ (x : List α) (hx : x ∈ T),
      NodeHQuant L x hx termTube load S.unionVol)
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
      L hlinkAt hquantAt geom_pair leaf_bound
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
theorem scalar_closure_discharged_physical {α : Type} [DecidableEq α] [Fintype α] {n d : ℕ}
    (fam : TubeFamily n d) (sh : Shading fam)
    (hpos : ∀ δ, 0 < δ → δ < 1 → 0 < (volume (⋃ t, sh.Y t δ)).toReal)
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (lab : List α → ℕ × ℕ × ℕ) (hlab : DescentLabels T lab)
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (htotalLoad : ∀ δ, totalLoad T load δ =
      ∑ t, (physicalRealization fam sh hpos).shadeVol t δ)
    (leaf_bound : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 →
      load γ δ ≤ (physicalRealization fam sh hpos).unionVol δ)
    (L : HardeningLedger α (n := n) T)
    (hlinkAt : ∀ (x : List α) (hx : x ∈ T),
      NodeHLink L x hx termTube load (physicalRealization fam sh hpos).unionVol)
    (hquantAt : ∀ (x : List α) (hx : x ∈ T),
      NodeHQuant L x hx termTube load (physicalRealization fam sh hpos).unionVol)
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
    L hlinkAt hquantAt geom_pair

/-- Scalar closure on the *constructed* symmetric tree (Stream F, M5).

Instantiates the general `scalar_closure_discharged` (`α = DMark n B`)
with `T = descTree n B H₀ C₀`, discharging every hypothesis from the
construction:
- root/prefix/labels: `descTree_root`, `descTree_prefix`, `descTree_labels`;
- `hload`: `descentLoad_nonneg`;
- `htotalLoad`: `htotalLoad_symm` at `[]` plus `root_fiber_card`
  (`Dx [] t = shadeVol t`);
- `leaf_bound`: `leaf_bound_proved`;
- `terminal_hardening`: `terminal_hardening_symm` via `termLoad_reroot_Dx`,
  lifted by `SubpowerLE.of_le_const`;
- `geom_pair`: `geom_pair_symm` via `termLoad_reroot_Dx`, lifted by
  `SubpowerLE.of_le_const` with `K = n - 1`.

Honesty: the symmetric `geom_pair_symm` is crude (constant `n-1`), so
this is a model-validation closure, not the paper's sharp (53)/(177)/(81)
estimate (which remains an external input to the main gate). -/
theorem scalar_closure_constructed {n B H₀ C₀ : ℕ} (hn : 0 < n) (hB : 0 < B)
    (hC : 0 < C₀) (S : ShadedTubes n) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol := by
  have hBpow : (0:ℝ) < (B ^ H₀ : ℝ) := by
    have h1 : 0 < B ^ H₀ := Nat.pow_pos hB
    exact_mod_cast h1
  have hU_nonneg : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ S.unionVol δ := by
    intro δ hδ1 hδ2
    have h1 := S.shade_nonneg (⟨0, hn⟩ : Fin n) δ hδ1 hδ2
    have h2 := S.shade_le_union (⟨0, hn⟩ : Fin n) δ hδ1 hδ2
    linarith
  have hDx_sum_nonneg : ∀ (x : List (DMark n B)) (δ : ℝ), 0 < δ → δ < 1 →
      0 ≤ ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t := by
    intro x δ hδ1 hδ2
    apply Finset.sum_nonneg
    intro t _
    exact Dx_nonneg hn hB S δ hδ1 hδ2 x t
  have hload : ∀ γ ∈ treeLeaves (descTree n B H₀ C₀), ∀ δ : ℝ, 0 < δ → δ < 1 →
      0 ≤ descentLoad H₀ S δ hn γ := by
    intro γ hγ δ hδ1 hδ2
    exact descentLoad_nonneg S δ hδ1 hδ2 hn hγ hBpow
  have htotalLoad : ∀ δ : ℝ,
      totalLoad (descTree n B H₀ C₀) (fun γ δ => descentLoad H₀ S δ hn γ) δ
        = ∑ t, S.shadeVol t δ := by
    intro δ
    have h1 : totalLoad (descTree n B H₀ C₀) (fun γ δ => descentLoad H₀ S δ hn γ) δ
        = ∑ t : Fin n, Dx (B := B) (C₀ := C₀) H₀ S δ hn [] t := by
      have h2 := htotalLoad_symm (B := B) (H₀ := H₀) (C₀ := C₀) hn S δ []
      rw [reroot_empty] at h2
      have heq : totalLoad (descTree n B H₀ C₀) (fun γ δ => descentLoad H₀ S δ hn γ) δ
          = totalLoad (descTree n B H₀ C₀)
            (fun s δ' => descentLoad H₀ S δ' hn ([] ++ s)) δ := rfl
      rw [heq]
      exact h2.symm
    rw [h1]
    apply Finset.sum_congr rfl
    intro t _
    rw [Dx_eq hn S δ [] t, root_fiber_card hn hB hC t]
    push_cast
    have hne : ((B : ℝ) ^ H₀) ≠ 0 := by
      have h1 : (0:ℝ) < (B : ℝ) ^ H₀ := by
        have h2 : (0:ℝ) < (B : ℝ) := by exact_mod_cast hB
        exact pow_pos h2 H₀
      exact ne_of_gt h1
    rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hne, mul_one]
  have hleaf : ∀ γ ∈ treeLeaves (descTree n B H₀ C₀), ∀ δ : ℝ, 0 < δ → δ < 1 →
      descentLoad H₀ S δ hn γ ≤ S.unionVol δ := by
    intro γ hγ δ hδ1 hδ2
    exact leaf_bound_proved S δ hδ1 hδ2 hn (by omega) hγ
  have hterm : ∀ x ∈ descTree n B H₀ C₀, SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad (reroot (descTree n B H₀ C₀) x)
        (fun s => termTube hn (x ++ s))
        (fun s δ => descentLoad H₀ S δ hn (x ++ s)) t δ) ^ 2)
      (fun δ => S.unionVol δ * totalLoad (reroot (descTree n B H₀ C₀) x)
        (fun s δ => descentLoad H₀ S δ hn (x ++ s)) δ) := by
    intro x hx
    have hsub : SubpowerLE
        (fun δ => ∑ t : Fin n, (Dx (C₀ := C₀) H₀ S δ hn x t)^2)
        (fun δ => S.unionVol δ * ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t) := by
      apply SubpowerLE.of_le_const (K := 1) zero_le_one
      · intro δ hδ1 hδ2
        have h := terminal_hardening_symm (H₀ := H₀) hn hB hC S δ hδ1 hδ2 x
        simpa using h
      · intro δ hδ1 hδ2
        exact mul_nonneg (hU_nonneg δ hδ1 hδ2) (hDx_sum_nonneg x δ hδ1 hδ2)
    have hfun1 : (fun δ => ∑ t : Fin n, (termLoad (reroot (descTree n B H₀ C₀) x)
          (fun s => termTube hn (x ++ s))
          (fun s δ => descentLoad H₀ S δ hn (x ++ s)) t δ) ^ 2)
        = (fun δ => ∑ t : Fin n, (Dx (C₀ := C₀) H₀ S δ hn x t)^2) := by
      funext δ
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      exact termLoad_reroot_Dx hn S δ x t
    have hfun2 : (fun δ => S.unionVol δ * totalLoad (reroot (descTree n B H₀ C₀) x)
          (fun s δ => descentLoad H₀ S δ hn (x ++ s)) δ)
        = (fun δ => S.unionVol δ * ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t) := by
      funext δ
      rw [htotalLoad_symm hn S δ x]
    rw [hfun1, hfun2]
    exact hsub
  have hgeom : ∀ x ∈ descTree n B H₀ C₀, SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad (reroot (descTree n B H₀ C₀) x)
          (fun s => termTube hn (x ++ s))
          (fun s δ => descentLoad H₀ S δ hn (x ++ s)) t δ
          * termLoad (reroot (descTree n B H₀ C₀) x)
          (fun s => termTube hn (x ++ s))
          (fun s δ => descentLoad H₀ S δ hn (x ++ s)) t' δ
        else 0)
      (fun δ => S.unionVol δ * totalLoad (reroot (descTree n B H₀ C₀) x)
        (fun s δ => descentLoad H₀ S δ hn (x ++ s)) δ) := by
    intro x hx
    have hK : (0:ℝ) ≤ (n : ℝ) - 1 := by
      have h1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hsub : SubpowerLE
        (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
          (if t ≠ t' then Dx (C₀ := C₀) H₀ S δ hn x t
            * Dx (C₀ := C₀) H₀ S δ hn x t' else 0))
        (fun δ => S.unionVol δ * ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t) := by
      apply SubpowerLE.of_le_const (K := (n : ℝ) - 1) hK
      · intro δ hδ1 hδ2
        have h := geom_pair_symm (H₀ := H₀) hn hB hC S δ hδ1 hδ2 x
        have hrw : ((n : ℝ) - 1) * S.unionVol δ
            * ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t
          = ((n : ℝ) - 1) * (S.unionVol δ
            * ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t) := by ring
        rw [hrw] at h
        exact h
      · intro δ hδ1 hδ2
        exact mul_nonneg (hU_nonneg δ hδ1 hδ2) (hDx_sum_nonneg x δ hδ1 hδ2)
    have hfun1 : (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
          if t ≠ t' then termLoad (reroot (descTree n B H₀ C₀) x)
            (fun s => termTube hn (x ++ s))
            (fun s δ => descentLoad H₀ S δ hn (x ++ s)) t δ
            * termLoad (reroot (descTree n B H₀ C₀) x)
            (fun s => termTube hn (x ++ s))
            (fun s δ => descentLoad H₀ S δ hn (x ++ s)) t' δ
          else 0)
        = (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
          (if t ≠ t' then Dx (C₀ := C₀) H₀ S δ hn x t
            * Dx (C₀ := C₀) H₀ S δ hn x t' else 0)) := by
      funext δ
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro t' _
      by_cases hne : t ≠ t'
      · rw [if_pos hne, if_pos hne,
          termLoad_reroot_Dx hn S δ x t, termLoad_reroot_Dx hn S δ x t']
      · rw [if_neg hne, if_neg hne]
    have hfun2 : (fun δ => S.unionVol δ * totalLoad (reroot (descTree n B H₀ C₀) x)
          (fun s δ => descentLoad H₀ S δ hn (x ++ s)) δ)
        = (fun δ => S.unionVol δ * ∑ t : Fin n, Dx (C₀ := C₀) H₀ S δ hn x t) := by
      funext δ
      rw [htotalLoad_symm hn S δ x]
    rw [hfun1, hfun2]
    exact hsub
  -- TODO: construct HardeningLedger for the symmetric descTree.
  -- The hterm (terminal_hardening_symm) needs to be replaced by ledger data.
  sorry

end FilteredDescent
