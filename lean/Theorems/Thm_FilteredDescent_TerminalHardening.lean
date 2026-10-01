import Definitions.Def_FilteredDescent_Packet
import Definitions.Def_FilteredDescent_Subpower
import Theorems.Thm_FilteredDescent_R5
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# Terminal hardening via common-source aggregation (paper §10.3, (148)–(153))

Faithful formalization of the paper's "Common-source aggregation"
argument, which closes the duplicate subgate.  The paper's chain:

* (148): the source-compatible hardening `D_T(x) ≲ δ^{-o(1)} B_I^{pred}`;
* (149): `D_T(x) ≤ F_T(x) · B_I^{pred}` where
  `F_T(x) := #{b ∈ ch(r∗) : D_{b,T}(x) > 0}`;
* (150)–(151): for fixed `(θ,j,c)` the aggregate comparison, an
  application of R5 (paper (25)) to the disjoint common-source aggregate;
* (152): the coarse-carrier count `|C_κ| ≤ C_d κ^{-C_d} = δ^{-o(1)}`;
* (153): `D_T(x) ≤ Σ_{θ,j,c} W_{θ,j,c}(x) ≲ |C_κ| B_I^{pred}`.

Model hypotheses (stated honestly): the `(θ,j,c)` disintegration
(`cls`, `slotOf`, per-class packet data `w`/`A`/`α`), the aggregate-level
predecessor invariant `hlink` (the class's active-child mass is
predecessor-bounded packet mass — the finite form of (150)–(151)), the
branch-density comparability `hquant` (retained children have comparable
density — the finite form of the hereditary branch-density range), and the
coarse-carrier count `hcard` (the imported (152) subpower bound
`|C_κ| = δ^{-o(1)}`; we name it rather than proving it for a concrete
`κ`-net).  The R5 marginal bound `r5_marginal_bound` (paper (25)) is
genuinely applied once per class.

Fidelity note: the paper works pointwise in `x`; we work at the
integrated pair-sum level, with one spatial cell's mass as a real number
depending on the scale `δ`.
-/

namespace FilteredDescent

/-- History count `F_T(δ) := #{b : D_{b,T}(δ) > 0}`.  Paper (149). -/
noncomputable def histCount {m n : ℕ} (Db : Fin m → Fin n → ℝ → ℝ) (t : Fin n)
    (δ : ℝ) : ℝ :=
  ((Finset.univ.filter (fun b : Fin m => 0 < Db b t δ)).card : ℝ)

/-- Per-class history count for the `(θ,j,c)` disintegration of §10.3:
the active children whose class mark is `k`. -/
noncomputable def classCount {m n : ℕ} {K : Type*} [DecidableEq K]
    (Db : Fin m → Fin n → ℝ → ℝ) (cls : Fin m → K) (k : K) (t : Fin n)
    (δ : ℝ) : ℝ :=
  ((Finset.univ.filter (fun b : Fin m => cls b = k ∧ 0 < Db b t δ)).card : ℝ)

/-- Repartition of the history count over the class alphabet:
`F_T = Σ_k F_{k,T}`.  The `(θ,j,c)` classes partition the active
children (paper §10.3: the `C_{b,c}` disintegrate each child's cylinder). -/
theorem histCount_eq_sum_classCount {m n : ℕ} {K : Type*} [Fintype K]
    [DecidableEq K] (Db : Fin m → Fin n → ℝ → ℝ) (cls : Fin m → K)
    (t : Fin n) (δ : ℝ) :
    histCount Db t δ = ∑ k : K, classCount Db cls k t δ := by
  have hfib : ∀ k : K,
      (Finset.univ.filter (fun b : Fin m => cls b = k ∧ 0 < Db b t δ)).card
        = ((Finset.univ.filter (fun b : Fin m => 0 < Db b t δ)).filter
          (fun b => cls b = k)).card := by
    intro k
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  have key := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun b : Fin m => 0 < Db b t δ)) (t := Finset.univ)
    (g := cls) (fun b _ => Finset.mem_univ (cls b)) (fun _ => (1 : ℕ))
  unfold histCount classCount
  rw [← Nat.cast_sum]
  congr 1
  conv_lhs => rw [Finset.card_eq_sum_ones]
  rw [← key]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hfib k, Finset.card_eq_sum_ones]

/-- Terminal hardening (paper §10.3, (148)–(153)).

The duplicate-branch quadratic load `Σ_T D_T(δ)^2` is subpower-dominated
by the predecessor bound times the total load.  Hypotheses:

* `Db`, `hDb_nn`, `hD`: per-root-child loads, nonnegative, summing to `D`
  (paper (145));
* `hDb_le`: every retained root child is a proper vertex, so the
  predecessor invariant gives `D_{b,T} ≤ B_I^{pred}` (paper (149));
* `hBpred_nn`: the predecessor bound is nonnegative on `(0,1)`;
* `cls`, `slotOf`: the `(θ,j,c)` class disintegration (model hypothesis);
* `hr`, `w`, `hw`, `hW`, `A`, `hAne`, `α`, `hα`, `hαpos`: per-class packet
  data instantiating `r5_marginal_bound` (paper (25));
* `hlink`: the class's active-child mass is predecessor-bounded packet
  mass — the aggregate-level predecessor invariant on the disjoint
  `(θ,j,c)` aggregate, i.e. the finite form of (150)–(151) (model
  hypothesis);
* `c₀`, `hc₀`, `hquant`: branch-density comparability — retained children
  have comparable density (model hypothesis);
* `hcard`: the coarse-carrier count `|C_κ| ≤ C_d κ^{-C_d} = δ^{-o(1)}`,
  paper (152), imported as a named subpower bound. -/
theorem terminal_hardening {n m r : ℕ} {K : Type*} [Fintype K] [DecidableEq K]
    (D : Fin n → ℝ → ℝ) (Bpred : ℝ → ℝ)
    (Db : Fin m → Fin n → ℝ → ℝ)
    (hDb_nn : ∀ b t δ, 0 < δ → δ < 1 → 0 ≤ Db b t δ)
    (hD : ∀ t δ, D t δ = ∑ b, Db b t δ)
    (hDb_le : ∀ b t δ, 0 < δ → δ < 1 → Db b t δ ≤ Bpred δ)
    (hBpred_nn : ∀ δ, 0 < δ → δ < 1 → 0 ≤ Bpred δ)
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
    (hquant : ∀ k b t δ, 0 < δ → δ < 1 → cls b = k → 0 < Db b t δ
      → c₀ * Bpred δ ≤ Db b t δ)
    (hcard : SubpowerLE (fun _ : ℝ => (Fintype.card K : ℝ)) (fun _ => 1)) :
    SubpowerLE (fun δ => ∑ T : Fin n, (D T δ)^2)
      (fun δ => Bpred δ * ∑ T : Fin n, D T δ) := by
  -- Paper (149): `D_T ≤ F_T · B_I^{pred}` (sum over active children).
  have h149 : ∀ t : Fin n, ∀ δ : ℝ, 0 < δ → δ < 1 →
      D t δ ≤ histCount Db t δ * Bpred δ := by
    intro t δ hδ0 hδ1
    have hsplit :
        ∑ b ∈ Finset.univ.filter (fun b : Fin m => 0 < Db b t δ), Db b t δ
          = ∑ b : Fin m, Db b t δ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      by_cases hb : 0 < Db b t δ
      · rw [if_pos hb]
      · rw [if_neg hb]
        have hnn := hDb_nn b t δ hδ0 hδ1
        have hle : Db b t δ ≤ 0 := le_of_not_gt hb
        linarith
    rw [hD t δ, ← hsplit]
    unfold histCount
    calc ∑ b ∈ Finset.univ.filter (fun b : Fin m => 0 < Db b t δ), Db b t δ
        ≤ ((Finset.univ.filter (fun b : Fin m => 0 < Db b t δ)).card) •
          Bpred δ :=
          Finset.sum_le_card_nsmul _ _ _ (fun b _ => hDb_le b t δ hδ0 hδ1)
      _ = ((Finset.univ.filter (fun b : Fin m => 0 < Db b t δ)).card : ℝ) *
          Bpred δ := by
          rw [nsmul_eq_mul]
  -- R5 (paper (25)) applied once per class, with the retained mass `α`
  -- multiplied out: the class's packet mass at slot `slotOf k` is at most
  -- the base-law ratio `w_k t / Σ_i w_k i`.
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
  -- Per-class count `F_k ≤ 1/c₀`: the aggregate predecessor bound `hlink`
  -- against the comparability lower bound `hquant`.
  have hFk : ∀ k : K, ∀ t : Fin n, ∀ δ : ℝ, 0 < δ → δ < 1 →
      classCount Db cls k t δ ≤ 1 / c₀ := by
    intro k t δ hδ0 hδ1
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
    · -- `Bpred δ = 0`: every child load vanishes, so the class count is `0`.
      have hSk : Finset.univ.filter (fun b : Fin m => cls b = k ∧ 0 < Db b t δ)
          = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro b _
        simp only [not_and]
        intro _
        have h1 := hDb_le b t δ hδ0 hδ1
        rw [← hB0] at h1
        exact not_lt_of_ge h1
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
  -- Aggregate over classes: `F_T ≤ (card K)/c₀` (paper (153), raw form).
  have hFbound : ∀ t : Fin n, ∀ δ : ℝ, 0 < δ → δ < 1 →
      histCount Db t δ ≤ (Fintype.card K : ℝ) / c₀ := by
    intro t δ hδ0 hδ1
    rw [histCount_eq_sum_classCount (K := K) (cls := cls)]
    calc ∑ k : K, classCount Db cls k t δ
        ≤ ∑ _k : K, (1 / c₀) :=
          Finset.sum_le_sum (fun k _ => hFk k t δ hδ0 hδ1)
      _ = (Fintype.card K : ℝ) / c₀ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hDt_nn : ∀ t : Fin n, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ D t δ := by
    intro t δ hδ0 hδ1
    rw [hD t δ]
    exact Finset.sum_nonneg (fun b _ => hDb_nn b t δ hδ0 hδ1)
  -- Finale: route the class count through the (152) subpower count `hcard`.
  intro ε hε
  obtain ⟨Cκ, hCκ, hκ⟩ := hcard ε hε
  refine ⟨Cκ / c₀, div_nonneg hCκ (le_of_lt hc₀), fun δ hδ0 hδ1 => ?_⟩
  have hK : (Fintype.card K : ℝ) ≤ Cκ * δ ^ (-ε) := by
    have h := hκ δ hδ0 hδ1
    simpa using h
  have hKle : (Fintype.card K : ℝ) / c₀ ≤ (Cκ * δ ^ (-ε)) / c₀ := by
    rw [div_le_iff₀ hc₀, div_mul_cancel₀ _ (ne_of_gt hc₀)]
    exact hK
  have hYnn : 0 ≤ Bpred δ * ∑ t : Fin n, D t δ :=
    mul_nonneg (hBpred_nn δ hδ0 hδ1)
      (Finset.sum_nonneg (fun t _ => hDt_nn t δ hδ0 hδ1))
  have hsq : ∀ t : Fin n,
      (D t δ)^2 ≤ (Fintype.card K / c₀) * (Bpred δ * D t δ) := by
    intro t
    calc (D t δ)^2 = D t δ * D t δ := by ring
      _ ≤ (histCount Db t δ * Bpred δ) * D t δ :=
          mul_le_mul_of_nonneg_right (h149 t δ hδ0 hδ1) (hDt_nn t δ hδ0 hδ1)
      _ = histCount Db t δ * (Bpred δ * D t δ) := by ring
      _ ≤ ((Fintype.card K)/c₀) * (Bpred δ * D t δ) :=
          mul_le_mul_of_nonneg_right (hFbound t δ hδ0 hδ1)
            (mul_nonneg (hBpred_nn δ hδ0 hδ1) (hDt_nn t δ hδ0 hδ1))
  have hsum : ∑ t : Fin n, (D t δ)^2
      ≤ (Fintype.card K / c₀) * (Bpred δ * ∑ t : Fin n, D t δ) := by
    have h1 : ∀ t : Fin n, (Fintype.card K / c₀) * (Bpred δ * D t δ)
        = ((Fintype.card K / c₀) * Bpred δ) * D t δ := fun t => by ring
    calc ∑ t : Fin n, (D t δ)^2
        ≤ ∑ t : Fin n, ((Fintype.card K / c₀) * (Bpred δ * D t δ)) :=
          Finset.sum_le_sum (fun t _ => hsq t)
      _ = ∑ t : Fin n, (((Fintype.card K / c₀) * Bpred δ) * D t δ) :=
          Finset.sum_congr rfl (fun t _ => h1 t)
      _ = ((Fintype.card K / c₀) * Bpred δ) * ∑ t : Fin n, D t δ :=
          (Finset.mul_sum _ _ _).symm
      _ = (Fintype.card K / c₀) * (Bpred δ * ∑ t : Fin n, D t δ) := by ring
  calc ∑ T : Fin n, (D T δ)^2
      ≤ (Fintype.card K / c₀) * (Bpred δ * ∑ T : Fin n, D T δ) := hsum
    _ ≤ ((Cκ * δ^(-ε)) / c₀) * (Bpred δ * ∑ T : Fin n, D T δ) :=
        mul_le_mul_of_nonneg_right hKle hYnn
    _ = (Cκ / c₀) * δ^(-ε) * (Bpred δ * ∑ T : Fin n, D T δ) := by ring

end FilteredDescent
