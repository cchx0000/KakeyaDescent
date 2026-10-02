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

/-! ## P1-4: Subpower-fused node hardening -/

/-- Rpow product: `δ^{-ε/2} * δ^{-ε/2} = δ^{-ε}` for `δ > 0`. -/
theorem rpow_half_add (δ ε : ℝ) (hδ0 : 0 < δ) :
    δ ^ (-(ε/2)) * δ ^ (-(ε/2)) = δ ^ (-ε) := by
  rw [← Real.rpow_add hδ0]
  congr 1
  ring

/-- Class-count bound (paper (153), from (150)-(151)): `histCount ≤ card K / c₀`.

Uses ORIGINAL `hlink`/`hquant` with `Bpred` (not inflated); independent of
the (149) predecessor bound. Adapted from stream B's `hFk`/`hFbound`. -/
theorem histCount_le_card_div {n : ℕ} {K : Type*} [Fintype K] [DecidableEq K]
    {m r : ℕ} (Db : Fin m → Fin n → ℝ → ℝ)
    (_hDb_nn : ∀ b t δ, 0 < δ → δ < 1 → 0 ≤ Db b t δ)
    (Bpred : ℝ → ℝ) (hBpred_nn : ∀ δ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (cls : Fin m → K) (slotOf : K → Fin r) (hr : 0 < r)
    (w : K → Fin n → ℝ) (hw : ∀ k i, 0 ≤ w k i) (hW : ∀ k, 0 < ∑ i, w k i)
    (A : K → Finset (Fin r → Fin n)) (hAne : ∀ k, (A k).Nonempty)
    (α : K → ℝ) (hα : ∀ k, α k = retainedMass (w k) (A k))
    (hαpos : ∀ k, 0 < α k)
    (hlink : ∀ k t δ, 0 < δ → δ < 1 →
      ∑ b ∈ Finset.univ.filter (fun b : Fin m => cls b = k ∧ 0 < Db b t δ),
        Db b t δ
        ≤ Bpred δ * ∑ U ∈ A k,
          (if U (slotOf k) = t then packetLaw (w k) U else 0))
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hquant : ∀ k (b : Fin m) t δ, 0 < δ → δ < 1 → cls b = k →
      0 < Db b t δ → c₀ * Bpred δ ≤ Db b t δ)
    (t : Fin n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    histCount Db t δ ≤ (Fintype.card K : ℝ) / c₀ := by
  -- Per-class: classCount ≤ 1/c₀ (stream B's hFk).
  have hmass : ∀ k : K, ∀ t : Fin n,
      ∑ U ∈ A k, (if U (slotOf k) = t then packetLaw (w k) U else 0)
        ≤ w k t / ∑ i, w k i := by
    intro k t
    have hr5 := (r5_marginal_bound hr (w k) (hw k) (hW k) (slotOf k) t).2
      (A k) (hAne k) (α k) (hα k) (hαpos k)
    have hαne : α k ≠ 0 := ne_of_gt (hαpos k)
    have hle := (div_le_iff₀ (hαpos k)).mp hr5
    have hcan : (1 / α k) * (w k t / ∑ i, w k i) * α k
        = w k t / ∑ i, w k i := by
      calc (1 / α k) * (w k t / ∑ i, w k i) * α k
          = (w k t / ∑ i, w k i) * ((1 / α k) * α k) := by ring
        _ = (w k t / ∑ i, w k i) * 1 := by rw [one_div_mul_cancel hαne]
        _ = w k t / ∑ i, w k i := by ring
    exact hle.trans_eq hcan
  have hFk : ∀ k : K, classCount Db cls k t δ ≤ 1 / c₀ := by
    intro k
    have hup :
        ∑ b ∈ Finset.univ.filter (fun b : Fin m => cls b = k ∧ 0 < Db b t δ),
          Db b t δ
          ≤ Bpred δ * (w k t / ∑ i, w k i) :=
      (hlink k t δ hδ0 hδ1).trans
        (mul_le_mul_of_nonneg_left (hmass k t) (hBpred_nn δ hδ0 hδ1))
    have hlow : classCount Db cls k t δ * (c₀ * Bpred δ)
        ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin m => cls b = k ∧ 0 < Db b t δ),
          Db b t δ := by
      have h := Finset.card_nsmul_le_sum
        (Finset.univ.filter (fun b : Fin m => cls b = k ∧ 0 < Db b t δ))
        (fun b => Db b t δ) (c₀ * Bpred δ) (by
          intro b hb
          rw [Finset.mem_filter] at hb
          exact hquant k b t δ hδ0 hδ1 hb.2.1 hb.2.2)
      rw [nsmul_eq_mul] at h
      unfold classCount
      exact h
    rcases eq_or_lt_of_le (hBpred_nn δ hδ0 hδ1) with hB0 | hBpos
    · -- Bpred = 0: class count is 0.
      have hSk : Finset.univ.filter (fun b : Fin m => cls b = k ∧ 0 < Db b t δ)
          = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro b _
        simp only [not_and]
        intro hcls hbpos
        -- ∑ Db ≤ 0 (from hup with Bpred=0), but Db b t δ > 0 and others ≥ 0.
        have hsum0 : ∑ b' ∈ Finset.univ.filter
            (fun b' : Fin m => cls b' = k ∧ 0 < Db b' t δ), Db b' t δ ≤ 0 := by
          calc ∑ b' ∈ Finset.univ.filter
                (fun b' : Fin m => cls b' = k ∧ 0 < Db b' t δ), Db b' t δ
              ≤ Bpred δ * (w k t / ∑ i, w k i) := hup
            _ = 0 := by rw [← hB0]; ring
        have hmem : b ∈ Finset.univ.filter
            (fun b' : Fin m => cls b' = k ∧ 0 < Db b' t δ) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ b, hcls, hbpos⟩
        have hpos_sum : 0 < ∑ b' ∈ Finset.univ.filter
            (fun b' : Fin m => cls b' = k ∧ 0 < Db b' t δ), Db b' t δ := by
          apply Finset.sum_pos'
          · intro b' hb'
            rw [Finset.mem_filter] at hb'
            exact le_of_lt hb'.2.2
          · exact ⟨b, hmem, hbpos⟩
        linarith
      unfold classCount
      rw [hSk, Finset.card_empty, Nat.cast_zero]
      exact div_nonneg zero_le_one (le_of_lt hc₀)
    · have hchain : classCount Db cls k t δ * (c₀ * Bpred δ)
          ≤ Bpred δ * (w k t / ∑ i, w k i) := hlow.trans hup
      have h2 : (classCount Db cls k t δ * c₀) * Bpred δ
          ≤ (w k t / ∑ i, w k i) * Bpred δ := by
        calc (classCount Db cls k t δ * c₀) * Bpred δ
            = classCount Db cls k t δ * (c₀ * Bpred δ) := by ring
          _ ≤ Bpred δ * (w k t / ∑ i, w k i) := hchain
          _ = (w k t / ∑ i, w k i) * Bpred δ := by ring
      have hstep : classCount Db cls k t δ * c₀ ≤ w k t / ∑ i, w k i :=
        le_of_mul_le_mul_right h2 hBpos
      have hY1 : w k t / ∑ i, w k i ≤ 1 :=
        div_le_one_of_le₀
          (Finset.single_le_sum (fun i _ => hw k i) (Finset.mem_univ t))
          (le_of_lt (hW k))
      exact (le_div_iff₀ hc₀).mpr (hstep.trans hY1)
  -- Sum over K.
  rw [histCount_eq_sum_classCount (K := K) (cls := cls)]
  calc ∑ k : K, classCount Db cls k t δ
      ≤ ∑ _k : K, (1 / c₀) :=
        Finset.sum_le_sum (fun k _ => hFk k)
    _ = (Fintype.card K : ℝ) / c₀ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- Fused node hardening, full version (TODO_GUIDANCE P1-4).

Re-runs (149)-(153) with uniform subpower predecessor constant.
`hlink`/`hquant` keep original `Bpred`; (149) uses the inflated bound
from `uniform_proper_const`; extra factor absorbed into subpower ledger. -/
theorem node_hardening_subpower {α : Type} [Fintype α] [DecidableEq α]
    {n : ℕ} (T : Finset (List α))
    (hprefix : ∀ l ∈ T, ∀ p : List α, p <+: l → p ∈ T)
    (hnonroot : ∀ γ ∈ treeLeaves T, γ ≠ [])
    (termTube : List α → Fin n) (load : List α → ℝ → ℝ)
    (hload : ∀ γ ∈ treeLeaves T, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ)
    (Bpred : ℝ → ℝ)
    (hBpred_nn : ∀ δ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
    (Hpred_sub : ∀ a ∈ T, a ≠ [] →
      SubpowerLE (fun δ => nodeAgg T (fun γ => load γ δ) a) Bpred)
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
  intro ε hε
  obtain ⟨C₁, hC₁, hUnif⟩ :=
    uniform_proper_const T (fun γ δ => load γ δ) Bpred
      (fun δ hδ0 hδ1 => hBpred_nn δ hδ0 hδ1) Hpred_sub ε hε
  obtain ⟨Cκ, hCκ, hκ⟩ := H.hcard (ε/2) (half_pos hε)
  refine ⟨(Cκ / H.c₀) * C₁, mul_nonneg (div_nonneg hCκ (le_of_lt H.hc₀)) hC₁,
    fun δ hδ0 hδ1 => ?_⟩
  have hDb_le' : ∀ b : Fin (treeChildren T []).card, ∀ t : Fin n,
      rootChildDb T termTube load b t δ ≤ C₁ * δ^(-(ε/2)) * Bpred δ := by
    intro b t
    exact rootChildDb_le_Bpred T termTube load hload
      (fun δ => C₁ * δ^(-(ε/2)) * Bpred δ)
      (fun δ hδ0 hδ1 a ha hane => hUnif a ha hane δ hδ0 hδ1)
      b t δ hδ0 hδ1
  -- (149') via filtered sum, avoiding nested calc.
  have h149' : ∀ t : Fin n,
      termLoad T termTube load t δ ≤
        histCount (rootChildDb T termTube load) t δ *
          (C₁ * δ^(-(ε/2)) * Bpred δ) := by
    intro t
    have hD_eq := termLoad_eq_sum_rootChildDb T hprefix hnonroot termTube load t δ
    rw [hD_eq]
    have hsplit :
        ∑ b ∈ Finset.univ.filter
          (fun b : Fin (treeChildren T []).card =>
            0 < rootChildDb T termTube load b t δ),
          rootChildDb T termTube load b t δ
        = ∑ b : Fin (treeChildren T []).card,
          rootChildDb T termTube load b t δ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : 0 < rootChildDb T termTube load b t δ
      · rw [if_pos hb]
      · rw [if_neg hb]
        have hnn := rootChildDb_nonneg T termTube load hload b t δ hδ0 hδ1
        linarith [le_of_not_gt hb]
    rw [← hsplit]
    have hle := Finset.sum_le_card_nsmul
      (Finset.univ.filter
        (fun b : Fin (treeChildren T []).card =>
          0 < rootChildDb T termTube load b t δ))
      (fun b : Fin (treeChildren T []).card => rootChildDb T termTube load b t δ)
      (C₁ * δ^(-(ε/2)) * Bpred δ)
      (fun b _ => hDb_le' b t)
    rw [nsmul_eq_mul] at hle
    -- histCount unfolds to the filter card as a real.
    have hhc : histCount (rootChildDb T termTube load) t δ
        = ((Finset.univ.filter
            (fun b : Fin (treeChildren T []).card =>
              0 < rootChildDb T termTube load b t δ)).card : ℝ) := rfl
    rw [hhc]; exact hle
  -- histCount bound (original Bpred).
  have hHC : ∀ t : Fin n,
      histCount (rootChildDb T termTube load) t δ ≤
        (Cκ * δ^(-(ε/2))) / H.c₀ := by
    intro t
    have h1 := histCount_le_card_div
      (rootChildDb T termTube load)
      (fun b t δ hδ0 hδ1 =>
        rootChildDb_nonneg T termTube load hload b t δ hδ0 hδ1)
      Bpred hBpred_nn H.cls H.slotOf H.hr
      H.w H.hw H.hW H.A H.hAne H.α H.hα H.hαpos
      hlink H.c₀ H.hc₀ hquant t δ hδ0 hδ1
    have h2 : (Fintype.card H.K : ℝ) ≤ Cκ * δ^(-(ε/2)) := by
      have h := hκ δ hδ0 hδ1; simpa using h
    calc histCount (rootChildDb T termTube load) t δ
        ≤ (Fintype.card H.K : ℝ) / H.c₀ := h1
      _ ≤ (Cκ * δ^(-(ε/2))) / H.c₀ :=
          div_le_div_of_nonneg_right h2 (le_of_lt H.hc₀)
  -- D_t nonneg.
  have hDt_nn : ∀ t : Fin n, 0 ≤ termLoad T termTube load t δ := by
    intro t; unfold termLoad
    apply Finset.sum_nonneg; intro γ hγ
    rw [Finset.mem_filter] at hγ; exact hload γ hγ.1 δ hδ0 hδ1
  -- Per-term bound.
  have hsq : ∀ t : Fin n,
      (termLoad T termTube load t δ)^2 ≤
        (((Cκ / H.c₀) * C₁) * δ^(-ε) * Bpred δ) *
          termLoad T termTube load t δ := by
    intro t
    have h1 := h149' t
    have h2 := hHC t
    have h3 := hDt_nn t
    have hpow := rpow_half_add δ ε hδ0
    have hstep1 : (termLoad T termTube load t δ)^2 ≤
        (histCount (rootChildDb T termTube load) t δ *
          (C₁ * δ^(-(ε/2)) * Bpred δ)) *
          termLoad T termTube load t δ := by
      have : (termLoad T termTube load t δ)^2
          = termLoad T termTube load t δ * termLoad T termTube load t δ := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right h1 h3
    have hstep2 : (histCount (rootChildDb T termTube load) t δ *
          (C₁ * δ^(-(ε/2)) * Bpred δ)) *
          termLoad T termTube load t δ ≤
        ((((Cκ * δ^(-(ε/2))) / H.c₀) * (C₁ * δ^(-(ε/2)) * Bpred δ))) *
          termLoad T termTube load t δ := by
      apply mul_le_mul_of_nonneg_right _ h3
      apply mul_le_mul_of_nonneg_right h2
      apply mul_nonneg
      · exact mul_nonneg hC₁ (le_of_lt (Real.rpow_pos_of_pos hδ0 _))
      · exact hBpred_nn δ hδ0 hδ1
    have heq : (((Cκ * δ^(-(ε/2))) / H.c₀) * (C₁ * δ^(-(ε/2)) * Bpred δ))
        = (((Cκ / H.c₀) * C₁) * δ^(-ε) * Bpred δ) := by
      have hpp : (δ^(-(ε/2)) : ℝ) * δ^(-(ε/2)) = δ^(-ε) := hpow
      calc (((Cκ * δ^(-(ε/2))) / H.c₀) * (C₁ * δ^(-(ε/2)) * Bpred δ))
          = ((Cκ / H.c₀) * C₁) * (δ^(-(ε/2)) * δ^(-(ε/2))) * Bpred δ := by ring
        _ = ((Cκ / H.c₀) * C₁) * δ^(-ε) * Bpred δ := by rw [hpp]
    calc (termLoad T termTube load t δ)^2
        ≤ ((((Cκ * δ^(-(ε/2))) / H.c₀) * (C₁ * δ^(-(ε/2)) * Bpred δ))) *
          termLoad T termTube load t δ := hstep1.trans hstep2
      _ = ((((Cκ / H.c₀) * C₁) * δ^(-ε) * Bpred δ)) *
          termLoad T termTube load t δ := by rw [heq]
  -- Sum and factor.
  have hsum : ∑ t : Fin n, (termLoad T termTube load t δ)^2
      ≤ ((((Cκ / H.c₀) * C₁) * δ^(-ε) * Bpred δ)) *
        ∑ t : Fin n, termLoad T termTube load t δ := by
    have h : ∑ t : Fin n, (termLoad T termTube load t δ)^2
        ≤ ∑ t : Fin n, (((((Cκ / H.c₀) * C₁) * δ^(-ε) * Bpred δ)) *
          termLoad T termTube load t δ) :=
      Finset.sum_le_sum (fun t _ => hsq t)
    have hfac : ∑ t : Fin n, (((((Cκ / H.c₀) * C₁) * δ^(-ε) * Bpred δ)) *
          termLoad T termTube load t δ)
        = ((((Cκ / H.c₀) * C₁) * δ^(-ε) * Bpred δ)) *
          ∑ t : Fin n, termLoad T termTube load t δ := by
      rw [Finset.mul_sum]
    rw [hfac] at h; exact h
  -- Rewrite to SubpowerLE form.
  have htotal : ∑ t : Fin n, termLoad T termTube load t δ
      = totalLoad T load δ :=
    sum_termLoad_eq_totalLoad T termTube load δ
  rw [htotal] at hsum
  have hfinal : ((((Cκ / H.c₀) * C₁) * δ^(-ε) * Bpred δ)) * totalLoad T load δ
      = ((Cκ / H.c₀) * C₁) * δ^(-ε) * (Bpred δ * totalLoad T load δ) := by ring
  rw [hfinal] at hsum
  exact hsum

/-! ## P1-5: Per-subtree HardeningInputs from a single ledger -/

/-- Global hardening ledger (TODO_GUIDANCE P1-5).

Bundles the (θ,j,c) model data that is SHARED across all subtrees:
the class type `K`, packet weights `w`, packet sets `A`, quantum `c₀`,
etc.  Per-node variation is ONLY in the class assignment `clsAt`
for that node's children.  This ensures per-subtree `HardeningInputs`
are derived from the SAME ledger, not unrelated arbitrary models. -/
structure HardeningLedger (α : Type) [Fintype α] [DecidableEq α]
    {n : ℕ} (T : Finset (List α)) where
  K : Type
  [finK : Fintype K]
  [decK : DecidableEq K]
  r : ℕ
  hr : 0 < r
  w : K → Fin n → ℝ
  hw : ∀ k i, 0 ≤ w k i
  hW : ∀ k, 0 < ∑ i, w k i
  A : K → Finset (Fin r → Fin n)
  hAne : ∀ k, (A k).Nonempty
  αm : K → ℝ
  hα : ∀ k, αm k = retainedMass (w k) (A k)
  hαpos : ∀ k, 0 < αm k
  c₀ : ℝ
  hc₀ : 0 < c₀
  hcard : SubpowerLE (fun _ : ℝ => (Fintype.card K : ℝ)) (fun _ => 1)
  -- Per-node class assignment for the children of each node.
  clsAt : ∀ x ∈ T, Fin (treeChildren (reroot T x) []).card → K
  slotOf : K → Fin r

attribute [instance] HardeningLedger.finK HardeningLedger.decK

/-- Per-subtree `HardeningInputs` derived from the single global ledger. -/
noncomputable def hardeningInputsAt {α : Type} [Fintype α] [DecidableEq α]
    {n : ℕ} {T : Finset (List α)} (L : HardeningLedger α (n := n) T)
    (x : List α) (hx : x ∈ T) :
    HardeningInputs ((treeChildren (reroot T x) []).card) n where
  K := L.K
  r := L.r
  cls := L.clsAt x hx
  slotOf := L.slotOf
  hr := L.hr
  w := L.w
  hw := L.hw
  hW := L.hW
  A := L.A
  hAne := L.hAne
  α := L.αm
  hα := L.hα
  hαpos := L.hαpos
  c₀ := L.c₀
  hc₀ := L.hc₀
  hcard := L.hcard

end FilteredDescent
