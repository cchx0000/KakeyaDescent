import Definitions.Def_FilteredDescent_State
import Theorems.Thm_FilteredDescent_EndToEnd
import Theorems.Thm_FilteredDescent_FaithfulGate_Wired
import Theorems.Thm_FilteredDescent_FaithfulTreeBridge

/-!
# Faithful per-node hardening via stream B

Discharges the gate's `terminal_hardening` hypothesis (paper (148)) from
the (150)-(153) model inputs, via stream B's `terminal_hardening`.

For each node `x` of the faithful tree, the re-rooted subtree's
`termLoad` satisfies the `SubpowerLE` bound. The proof supplies stream B's
four key inputs:
- `hDb_nn`: from `childTermLoad_nonneg` (leaf nonnegativity);
- `hD`: from `sum_rootChildDb_eq` + `termLoad_eq_sum_childTermLoad`;
- `hDb_le`: from `childTermLoad_le_nodeAgg` + `Hpred` (paper (138));
- `∑ D = totalLoad`: from `sum_termLoad_eq_totalLoad` (fiber partition).
-/

namespace FilteredDescent

/-! ## Hardening inputs (paper (150)-(153)) -/

/-- Per-node hardening inputs for stream B's `terminal_hardening`
(paper (150)-(153)): the (θ,j,c) model data.

For a subtree rooted at `x`, these provide:
- `K`: the type index (θ,j carriers);
- `cls`: branch classification;
- `hlink`, `hquant`, `hcard`: the (150)/(151)/(152) bounds.

These are the paper's named model inputs; they are not proved here. -/
structure HardeningInputs (m n : ℕ) where
  K : Type
  [finK : Fintype K]
  [decK : DecidableEq K]
  r : ℕ
  cls : Fin m → K
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
  c₀ : ℝ
  hc₀ : 0 < c₀
  hcard : SubpowerLE (fun _ : ℝ => (Fintype.card K : ℝ)) (fun _ => 1)

attribute [instance] HardeningInputs.finK HardeningInputs.decK

/-! ## Node hardening lemmas -/

/-- `rootChildDb` nonnegativity from leaf-load nonnegativity. -/
theorem rootChildDb_nonneg {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (termTube : List α → Fin n)
    (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (b : Fin (treeChildren T []).card) (t : Fin n) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ rootChildDb T termTube load b t δ := by
  unfold rootChildDb
  exact childTermLoad_nonneg T termTube load hload _ t δ hδ0 hδ1

/-- `hD` for stream B: `termLoad` equals the sum of `rootChildDb` over
branches, via `sum_rootChildDb_eq` and `termLoad_eq_sum_childTermLoad`. -/
theorem termLoad_eq_sum_rootChildDb {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α))
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (hnonroot : ∀ γ ∈ treeLeaves T, γ ≠ [])
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (t : Fin n) (δ : ℝ) :
    termLoad T termTube load t δ
      = ∑ b : Fin (treeChildren T []).card, rootChildDb T termTube load b t δ := by
  rw [sum_rootChildDb_eq]
  exact termLoad_eq_sum_childTermLoad T hprefix termTube load hnonroot t δ

/-- `childTermLoad` is bounded by `nodeAgg` (sub-sum, needs `load ≥ 0`). -/
theorem childTermLoad_le_nodeAgg {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (termTube : List α → Fin n)
    (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (b : List α) (t : Fin n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    childTermLoad T termTube load b t δ
      ≤ nodeAgg T (fun γ => load γ δ) b := by
  unfold childTermLoad nodeAgg
  have hsub : (treeLeaves T).filter (fun γ => b <+: γ ∧ termTube γ = t)
      ⊆ (treeLeaves T).filter (fun γ => b <+: γ) := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ ⊢
    exact ⟨hγ.1, hγ.2.1⟩
  calc ∑ γ ∈ (treeLeaves T).filter (fun γ => b <+: γ ∧ termTube γ = t),
        load γ δ
      ≤ ∑ γ ∈ (treeLeaves T).filter (fun γ => b <+: γ), load γ δ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro γ hγ _
        rw [Finset.mem_filter] at hγ
        exact hload γ hγ.1 δ hδ0 hδ1
    _ = ∑ γ ∈ treeLeaves T, (if b <+: γ then load γ δ else 0) := by
        rw [Finset.sum_filter]

/-- `rootChildDb` bounded by `Bpred` via `Hpred` (paper (138)). -/
theorem rootChildDb_le_Bpred {α : Type} [DecidableEq α] {n : ℕ}
    (T : Finset (List α)) (termTube : List α → Fin n)
    (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (Hpred : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ a ∈ T, a ≠ [] →
      nodeAgg T (fun γ => load γ δ) a ≤ Bpred δ)
    (b : Fin (treeChildren T []).card) (t : Fin n) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    rootChildDb T termTube load b t δ ≤ Bpred δ := by
  unfold rootChildDb
  set cb := ((treeChildren T []).equivFin.symm b).val with hcb
  have hcb_mem : cb ∈ treeChildren T [] :=
    ((treeChildren T []).equivFin.symm b).property
  rw [treeChildren, Finset.mem_filter] at hcb_mem
  have hcb_ne : cb ≠ [] := by
    obtain ⟨_, _, hlen⟩ := hcb_mem
    intro h; rw [h] at hlen; simp at hlen
  calc childTermLoad T termTube load cb t δ
      ≤ nodeAgg T (fun γ => load γ δ) cb :=
        childTermLoad_le_nodeAgg T termTube load hload cb t δ hδ0 hδ1
    _ ≤ Bpred δ := Hpred δ hδ0 hδ1 cb hcb_mem.1 hcb_ne

/-- `∑ t, termLoad t = totalLoad`: partition leaves by `termTube`. -/
theorem sum_termLoad_eq_totalLoad {α : Type} [DecidableEq α] [Fintype α]
    {n : ℕ} (T : Finset (List α))
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ) (δ : ℝ) :
    (∑ t : Fin n, termLoad T termTube load t δ) = totalLoad T load δ := by
  unfold termLoad totalLoad
  have hdisj : ∀ t1 ∈ (Finset.univ : Finset (Fin n)),
      ∀ t2 ∈ (Finset.univ : Finset (Fin n)),
      t1 ≠ t2 → Disjoint
        ((treeLeaves T).filter (fun γ => termTube γ = t1))
        ((treeLeaves T).filter (fun γ => termTube γ = t2)) := by
    intro t1 _ t2 _ hne
    rw [Finset.disjoint_filter]
    intro γ _ h1 h2
    exact hne (h1.symm.trans h2)
  have hunion : (treeLeaves T).filter (fun _ => True)
      = (Finset.univ : Finset (Fin n)).biUnion
        (fun t => (treeLeaves T).filter (fun γ => termTube γ = t)) := by
    ext γ
    simp [Finset.mem_filter, Finset.mem_biUnion]
  have hLHS : (∑ t : Fin n,
      ∑ γ ∈ (treeLeaves T).filter (fun γ => termTube γ = t), load γ δ)
      = ∑ γ ∈ (Finset.univ : Finset (Fin n)).biUnion
        (fun t => (treeLeaves T).filter (fun γ => termTube γ = t)),
        load γ δ := by
    rw [Finset.sum_biUnion hdisj]
  rw [hLHS, ← hunion]
  simp

/-! ## Main: node hardening via stream B -/

/-- Node hardening via stream B (paper (148)): the lemmas above supply
`hDb_nn`, `hD`, `hDb_le`, and the `∑ D = totalLoad` identity. -/
theorem node_hardening_via_streamB {α : Type} [Fintype α] [DecidableEq α]
    {n : ℕ} (T : Finset (List α))
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (hnonroot : ∀ γ ∈ treeLeaves T, γ ≠ [])
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (hBpred_nn : ∀ δ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (Hpred : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ a ∈ T, a ≠ [] →
      nodeAgg T (fun γ => load γ δ) a ≤ Bpred δ)
    (H : HardeningInputs ((treeChildren T []).card) n)
    (hlink : ∀ k t δ, 0 < δ → δ < 1 →
      ∑ b ∈ Finset.univ.filter (fun b : Fin (treeChildren T []).card =>
        H.cls b = k ∧ 0 < rootChildDb T termTube load b t δ),
        rootChildDb T termTube load b t δ
        ≤ Bpred δ * ∑ U ∈ H.A k,
          (if U (H.slotOf k) = t then packetLaw (H.w k) U else 0))
    (hquant : ∀ k (b : Fin (treeChildren T []).card) t δ,
      0 < δ → δ < 1 → H.cls b = k →
      0 < rootChildDb T termTube load b t δ →
      H.c₀ * Bpred δ ≤ rootChildDb T termTube load b t δ) :
    SubpowerLE
      (fun δ => ∑ t : Fin n, (termLoad T termTube load t δ)^2)
      (fun δ => Bpred δ * totalLoad T load δ) := by
  have hB := terminal_hardening
    (D := fun t δ => termLoad T termTube load t δ)
    (Bpred := Bpred)
    (Db := rootChildDb T termTube load)
    (hDb_nn := fun b t δ hδ0 hδ1 =>
      rootChildDb_nonneg T termTube load hload b t δ hδ0 hδ1)
    (hD := fun t δ =>
      termLoad_eq_sum_rootChildDb T hprefix hnonroot termTube load t δ)
    (hDb_le := fun b t δ hδ0 hδ1 =>
      rootChildDb_le_Bpred T termTube load hload Bpred Hpred b t δ hδ0 hδ1)
    (hBpred_nn := hBpred_nn)
    (cls := H.cls) (slotOf := H.slotOf) (hr := H.hr)
    (w := H.w) (hw := H.hw) (hW := H.hW)
    (A := H.A) (hAne := H.hAne)
    (α := H.α) (hα := H.hα) (hαpos := H.hαpos)
    (hlink := hlink) (c₀ := H.c₀) (hc₀ := H.hc₀)
    (hquant := hquant) (hcard := H.hcard)
  apply SubpowerLE.congr_right _ hB
  intro δ
  rw [sum_termLoad_eq_totalLoad]

end FilteredDescent
