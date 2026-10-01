import Definitions.Def_FilteredDescent_Subpower
import Definitions.Def_FilteredDescent_Tree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# Faithful root-cross gate — shared definitions (paper §10, (136), (145))

Definitions shared by the faithful formalization of the paper's root-cross
gate (§10, formulas (135)–(153)):

* `termLoad`: the terminal-tube load `D_T(δ) = Σ_{γ : T(γ)=T} u_γ`, paper (145).
* `childTermLoad`: the per-root-child terminal load `D_{b,T}(δ)`, paper (145).
* `totalLoad`: the total leaf load `N(δ) = Σ_γ u_γ`; paper (136) `W_{r∗} = N_{I,k}`.
* `SubpowerLE.mono`: monotonicity of the subpower order in the dominated quantity.

Fidelity note: the paper works pointwise in the spatial variable `x`
(`u_γ(x)`, `D_T(x)`); we work at the integrated pair-sum level, i.e. with
one spatial cell's worth of mass as a real number depending on the scale
`δ`.  The paper's pointwise identities (137)–(147) imply ours by
integration over `x`.
-/

namespace FilteredDescent

/-- Terminal-tube load `D_T(δ) := Σ_{γ ∈ leaves, T(γ)=T} u_γ(δ)`.  Paper (145). -/
noncomputable def termLoad {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (termTube : List α → Fin n)
    (load : List α → ℝ → ℝ) (t : Fin n) (δ : ℝ) : ℝ :=
  ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), load γ δ

/-- Per-root-child terminal load `D_{b,T}(δ)`.  Paper (145). -/
noncomputable def childTermLoad {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (termTube : List α → Fin n)
    (load : List α → ℝ → ℝ) (b : List α) (t : Fin n) (δ : ℝ) : ℝ :=
  ∑ γ ∈ (treeLeaves T).filter (fun γ => b <+: γ ∧ termTube γ = t), load γ δ

/-- Total leaf load `N(δ) = Σ_γ u_γ(δ)`.  Paper (136): `W_{r∗} = N_{I,k}`. -/
noncomputable def totalLoad {α : Type} [DecidableEq α]
    (T : Finset (List α)) (load : List α → ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∑ γ ∈ treeLeaves T, load γ δ

theorem termLoad_nonneg {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (termTube : List α → Fin n)
    (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (t : Fin n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ termLoad T termTube load t δ := by
  unfold termLoad
  apply Finset.sum_nonneg
  intro γ hγ
  rw [Finset.mem_filter] at hγ
  exact hload γ hγ.1 δ hδ0 hδ1

theorem childTermLoad_nonneg {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (termTube : List α → Fin n)
    (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (b : List α) (t : Fin n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ childTermLoad T termTube load b t δ := by
  unfold childTermLoad
  apply Finset.sum_nonneg
  intro γ hγ
  rw [Finset.mem_filter] at hγ
  exact hload γ hγ.1 δ hδ0 hδ1

theorem totalLoad_nonneg {α : Type} [DecidableEq α]
    (T : Finset (List α)) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ totalLoad T load δ := by
  unfold totalLoad
  apply Finset.sum_nonneg
  intro γ hγ
  exact hload γ hγ δ hδ0 hδ1

/-- The terminal loads partition the total load: `Σ_T D_T = N`.
Paper (145): `Σ_T D_T = N_{I,k}`. -/
theorem totalLoad_eq_sum_termLoad {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (termTube : List α → Fin n)
    (load : List α → ℝ → ℝ) (δ : ℝ) :
    totalLoad T load δ = ∑ t : Fin n, termLoad T termTube load t δ := by
  unfold totalLoad termLoad
  rw [← Finset.sum_fiberwise_of_maps_to (g := termTube) (t := Finset.univ) (fun i _ => Finset.mem_univ _) _]

/-- Subpower domination is monotone in the dominated quantity. -/
theorem SubpowerLE.mono {x x' y : ℝ → ℝ}
    (hle : ∀ δ : ℝ, 0 < δ → δ < 1 → x δ ≤ x' δ)
    (h : SubpowerLE x' y) : SubpowerLE x y := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  exact ⟨C, hC, fun δ hδ0 hδ1 => le_trans (hle δ hδ0 hδ1) (hb δ hδ0 hδ1)⟩

end FilteredDescent
