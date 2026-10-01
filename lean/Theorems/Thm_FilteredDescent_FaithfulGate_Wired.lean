import Theorems.Thm_FilteredDescent_TerminalHardening
import Theorems.Thm_FilteredDescent_FaithfulGate
import Definitions.Def_FilteredDescent_Tree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic

/-!
# Faithful root-cross gate — wiring (paper §10, (135)–(153))

This file WIRES the two faithful streams together, with no edits to either
stream's files:

* Stream B (`Thm_FilteredDescent_TerminalHardening`): `terminal_hardening`,
  the (148)–(153) common-source aggregation through R5, stated for abstract
  per-child loads `Db : Fin m → Fin n → ℝ → ℝ`.
* Stream C (`Thm_FilteredDescent_FaithfulGate`): the faithful root-cross gate
  (135)–(147); its `Hdup_of_terminal_hardening` consumes a
  `terminal_hardening`-shaped input over the tree's `termLoad`.

The wiring instantiates Stream B with

* `D := fun t δ => termLoad T termTube load t δ` (paper (145)),
* `Db := rootChildDb T termTube load`: the per-root-child loads
  `childTermLoad` reindexed by `Fin m`, `m = #(root children)`, via
  `Finset.equivFin` (Stream B indexes children by `Fin m`; Stream C indexes
  them by the child node `b : List α`),

discharges `hD` from the exact fiber identity `termLoad_eq_sum_childTermLoad`
(paper (145): `D_T = Σ_b D_{b,T}`), discharges `hDb_le` from `Hpred` (every
root child is a proper vertex, so (138) gives `D_{b,T} ≤ W_b ≤ B^pred`; the
step `D_{b,T} ≤ W_b` is the trivial sub-sum, since the `termTube = t` fiber
sits inside the descendant leaves), and feeds the resulting `SubpowerLE`
into Stream C's `faithful_descent_step` (141)+(142).

## Honesty notes

* The `(θ,j,c)` model data (`cls`, `slotOf`, `w`, `A`, `α`, `hlink`,
  `hquant`, `hcard`) stay EXPLICITLY-NAMED hypotheses with paper citations
  ((150)–(153)); they are not proved here.
* `Hpred` (paper (138), the predecessor invariance / induction hypothesis)
  and `geom_pair` (paper (53)/(177)/(81), chosen per dimension at the call
  site) are likewise named, not proved.
* `hnonroot` excludes the degenerate one-node tree (root itself a leaf).
  The degenerate case is handled separately inside Stream C's exact
  identities, but the fiber identity `D_T = Σ_b D_{b,T}` needs the root to
  have children.
* `scalar_closure` (the `Thm_FilteredDescent_ScalarClosure` chain) still goes
  through the old simplified `root_cross_gate`; rewiring it to the faithful
  gate assembled here is future work and is NOT claimed.
-/

namespace FilteredDescent

/-- Per-root-child terminal load, reindexed by `Fin m` with
`m = (treeChildren T []).card`, so that Stream B's `terminal_hardening`
(stated for `Db : Fin m → Fin n → ℝ → ℝ`) can consume Stream C's
`childTermLoad` (indexed by the child node `b : List α`).  Paper (145). -/
noncomputable def rootChildDb {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (termTube : List α → Fin n) (load : List α → ℝ → ℝ) :
    Fin (treeChildren T []).card → Fin n → ℝ → ℝ :=
  fun i t δ =>
    childTermLoad T termTube load ((treeChildren T []).equivFin.symm i).val t δ

/-- The reindexed child loads sum back to the terminal load over the root
children. -/
theorem sum_rootChildDb_eq {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (t : Fin n) (δ : ℝ) :
    ∑ i : Fin (treeChildren T []).card, rootChildDb T termTube load i t δ
      = ∑ b ∈ treeChildren T [], childTermLoad T termTube load b t δ := by
  have h1 : (∑ i : Fin (treeChildren T []).card, rootChildDb T termTube load i t δ)
      = ∑ x : ↥(treeChildren T []), childTermLoad T termTube load x.val t δ :=
    Equiv.sum_comp (treeChildren T []).equivFin.symm
      (fun x : ↥(treeChildren T []) => childTermLoad T termTube load x.val t δ)
  rw [h1]
  exact Finset.sum_coe_sort (treeChildren T [])
    (fun b => childTermLoad T termTube load b t δ)

/-- Subpower domination is unchanged when the dominated quantity is rewritten
pointwise. -/
theorem SubpowerLE.congr_right {x y y' : ℝ → ℝ} (hy : ∀ δ, y δ = y' δ)
    (h : SubpowerLE x y) : SubpowerLE x y' := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
  rw [← hy δ]
  exact hb δ hδ0 hδ1

/-- The wired faithful gate: the full descent step (141)+(142), with Stream B's
`terminal_hardening` genuinely instantiated on the tree's per-child loads and
fed into Stream C's gate.

Named inputs (not proved here), with paper citations:

* `Hpred`: the predecessor invariance (138) — the induction hypothesis;
* `cls`, `slotOf`, `w`, `A`, `α`, `hlink`, `hquant`, `hcard`: the `(θ,j,c)`
  disintegration model data for the (150)–(153) common-source aggregation;
* `geom_pair`: the geometric pair estimate (53)/(177)/(81).

Structural inputs: `hroot`, `hprefix`, `hnonroot` (non-degenerate tree),
`hload`, `hBpred`. -/
theorem faithful_gate_wired {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (hroot : [] ∈ T)
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (hnonroot : ∀ γ ∈ treeLeaves T, γ ≠ [])
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (hBpred : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (Hpred : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ a ∈ T, a ≠ [] →
      nodeAgg T (fun γ => load γ δ) a ≤ Bpred δ)
    {K : Type*} [Fintype K] [DecidableEq K] {r : ℕ}
    (cls : Fin (treeChildren T []).card → K)
    (slotOf : K → Fin r) (hr : 0 < r)
    (w : K → Fin n → ℝ) (hw : ∀ k i, 0 ≤ w k i) (hW : ∀ k, 0 < ∑ i, w k i)
    (A : K → Finset (Fin r → Fin n)) (hAne : ∀ k, (A k).Nonempty)
    (α : K → ℝ) (hα : ∀ k, α k = retainedMass (w k) (A k))
    (hαpos : ∀ k, 0 < α k)
    (hlink : ∀ k t δ, 0 < δ → δ < 1 →
      ∑ b ∈ Finset.univ.filter
        (fun b : Fin (treeChildren T []).card =>
          cls b = k ∧ 0 < rootChildDb T termTube load b t δ),
        rootChildDb T termTube load b t δ
        ≤ Bpred δ * ∑ U ∈ A k,
          (if U (slotOf k) = t then packetLaw (w k) U else 0))
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hquant : ∀ k (b : Fin (treeChildren T []).card) t δ, 0 < δ → δ < 1 →
      cls b = k → 0 < rootChildDb T termTube load b t δ →
      c₀ * Bpred δ ≤ rootChildDb T termTube load b t δ)
    (hcard : SubpowerLE (fun _ : ℝ => (Fintype.card K : ℝ)) (fun _ => 1))
    (geom_pair : SubpowerLE
      (fun δ => ∑ t : Fin n, ∑ t' : Fin n,
        if t ≠ t' then termLoad T termTube load t δ * termLoad T termTube load t' δ
        else 0)
      (fun δ => Bpred δ * totalLoad T load δ)) :
    SubpowerLE (fun δ => (totalLoad T load δ) ^ 2)
      (fun δ => Bpred δ * totalLoad T load δ) := by
  -- Stream B's per-child nonnegativity, from the leaf-load nonnegativity.
  have hDb_nn : ∀ b : Fin (treeChildren T []).card, ∀ t : Fin n, ∀ δ : ℝ,
      0 < δ → δ < 1 → 0 ≤ rootChildDb T termTube load b t δ := by
    intro b t δ hδ0 hδ1
    show 0 ≤ childTermLoad T termTube load
      ((treeChildren T []).equivFin.symm b).val t δ
    exact childTermLoad_nonneg T termTube load hload _ t δ hδ0 hδ1
  -- Stream B's `hD`: the fiber identity `D_T = Σ_b D_{b,T}`, paper (145).
  have hD : ∀ t : Fin n, ∀ δ : ℝ, termLoad T termTube load t δ
      = ∑ i : Fin (treeChildren T []).card, rootChildDb T termTube load i t δ := by
    intro t δ
    rw [termLoad_eq_sum_childTermLoad T hprefix termTube load hnonroot t δ,
      sum_rootChildDb_eq T termTube load t δ]
  -- Stream B's `hDb_le`: every root child is a proper vertex, so `Hpred`
  -- (138) applies; the per-child terminal load is a sub-sum of the node
  -- aggregate.
  have hDb_le : ∀ b : Fin (treeChildren T []).card, ∀ t : Fin n, ∀ δ : ℝ,
      0 < δ → δ < 1 → rootChildDb T termTube load b t δ ≤ Bpred δ := by
    intro b t δ hδ0 hδ1
    show childTermLoad T termTube load
        ((treeChildren T []).equivFin.symm b).val t δ ≤ Bpred δ
    set c := ((treeChildren T []).equivFin.symm b).val with hc
    have hmem : c ∈ treeChildren T [] :=
      ((treeChildren T []).equivFin.symm b).property
    unfold treeChildren at hmem
    rw [Finset.mem_filter] at hmem
    obtain ⟨hbT, _, hlen⟩ := hmem
    have hbne : c ≠ [] := by
      intro hcon
      rw [hcon] at hlen
      simp at hlen
    have hle : (∑ γ ∈ (treeLeaves T).filter (fun γ => c <+: γ ∧ termTube γ = t),
          load γ δ)
        ≤ (∑ γ ∈ (treeLeaves T).filter (fun γ => c <+: γ), load γ δ) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro γ hγ
          rw [Finset.mem_filter] at hγ ⊢
          exact ⟨hγ.1, hγ.2.1⟩)
        (fun γ hγ _ => hload γ (Finset.mem_filter.mp hγ).1 δ hδ0 hδ1)
    have h1 : childTermLoad T termTube load c t δ
        = ∑ γ ∈ (treeLeaves T).filter (fun γ => c <+: γ ∧ termTube γ = t),
          load γ δ := rfl
    have h2 : nodeAgg T (fun γ => load γ δ) c
        = ∑ γ ∈ (treeLeaves T).filter (fun γ => c <+: γ), load γ δ := by
      show (∑ γ ∈ treeLeaves T, if c <+: γ then load γ δ else 0) = _
      rw [← Finset.sum_filter]
    have hsub : childTermLoad T termTube load c t δ
        ≤ nodeAgg T (fun γ => load γ δ) c := by
      rw [h1, h2]
      exact hle
    exact hsub.trans (Hpred δ hδ0 hδ1 c hbT hbne)
  -- Instantiate Stream B's `terminal_hardening` on the tree data, then
  -- rewrite its RHS `∑ t, D t δ` to `totalLoad` via (145).
  have hterm : SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad T termTube load t δ) ^ 2)
      (fun δ => Bpred δ * totalLoad T load δ) := by
    have hB := terminal_hardening
      (fun t : Fin n => fun δ : ℝ => termLoad T termTube load t δ) Bpred
      (rootChildDb T termTube load) hDb_nn hD hDb_le hBpred
      cls slotOf hr w hw hW A hAne α hα hαpos hlink c₀ hc₀ hquant hcard
    have hrhs : ∀ δ : ℝ,
        Bpred δ * ∑ t : Fin n, termLoad T termTube load t δ
          = Bpred δ * totalLoad T load δ := by
      intro δ
      congr 1
      exact (totalLoad_eq_sum_termLoad T termTube load δ).symm
    exact SubpowerLE.congr_right hrhs hB
  -- Feed the wired duplicate bound into Stream C's final gate (141)+(142).
  exact faithful_descent_step T hroot hprefix termTube load hload Bpred hBpred
    Hpred hterm geom_pair

end FilteredDescent
