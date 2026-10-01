import Definitions.Def_FilteredDescent_Pivot
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp

/-!
# M4 — Gram–Schmidt pivot dichotomy (paper (32)–(42))

For an ordered `r`-tuple of vectors with positive leading Gram
determinants, the pivots `p_j^2 = det G_{j+1} / det G_j` multiply to the
squared volume: `∏_j p_j^2 = (det S)^2`.  The dichotomy (paper (36)–(42)):
either every pivot is broad (`κ^2 ≤ p_j^2`), in which case
`κ^{2r} ≤ (det S)^2`, or some pivot is narrow.
-/

namespace FilteredDescent

theorem pivot_dichotomy {r : ℕ} (hr : 0 < r)
    (s : Fin r → (Fin r → ℝ))
    (hpos :
      ∀ k : Fin (r + 1), 0 < (gramTake s k.val (Nat.le_of_lt_succ k.isLt)).det)
    (κ : ℝ) (hκ : 0 < κ) :
    (∏ j : Fin r, pivotSq s j)
        = (Matrix.det (Matrix.of (fun a b : Fin r => s b a))) ^ 2 ∧
      ((∀ j : Fin r, κ ^ 2 ≤ pivotSq s j) ∨
        (∃ j : Fin r, pivotSq s j < κ ^ 2)) ∧
      ((∀ j : Fin r, κ ^ 2 ≤ pivotSq s j) →
        κ ^ (2 * r) ≤ (Matrix.det (Matrix.of (fun a b : Fin r => s b a))) ^ 2) := by
  set S : Matrix (Fin r) (Fin r) ℝ := Matrix.of (fun a b : Fin r => s b a) with hSdef
  -- `D k` is the `k`-th leading Gram determinant (junk value `1` off-range).
  set D : ℕ → ℝ := fun k => if hk : k ≤ r then (gramTake s k hk).det else 1 with hDdef
  -- positivity of the Gram determinants, for any proof of `k ≤ r`
  have hDpos : ∀ k : ℕ, ∀ hk : k ≤ r, (0:ℝ) < (gramTake s k hk).det := by
    intro k hk
    exact hpos ⟨k, Nat.lt_succ_of_le hk⟩
  have hDne : ∀ k : ℕ, ∀ hk : k ≤ r, (gramTake s k hk).det ≠ 0 :=
    fun k hk => ne_of_gt (hDpos k hk)
  have hDk : ∀ k : ℕ, ∀ hk : k ≤ r, D k = (gramTake s k hk).det :=
    fun k hk => dif_pos hk
  have hDne' : ∀ i : ℕ, D i ≠ 0 := by
    intro i
    by_cases hi : i ≤ r
    · rw [hDk i hi]; exact hDne i hi
    · rw [show D i = 1 from dif_neg hi]; exact one_ne_zero
  -- `D 0 = 1`: determinant of the `0 × 0` matrix
  have hD0 : (gramTake s 0 (Nat.zero_le r)).det = 1 := by
    have h1 : gramTake s 0 (Nat.zero_le r) = 1 := by
      ext i j
      exact Fin.elim0 i
    rw [h1, Matrix.det_one]
  -- the full Gram matrix factors as `S.transpose * S`
  have hgram : gramTake s r le_rfl = S.transpose * S := by
    ext i j
    simp only [hSdef, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, gramTake,
      Matrix.of_apply]
  have hDr : (gramTake s r le_rfl).det = S.det ^ 2 := by
    rw [hgram, Matrix.det_mul, Matrix.det_transpose, pow_two]
  -- telescoping product, by induction (avoids the `CommGroup` hypothesis of
  -- `Finset.prod_range_div`, which `ℝ` does not satisfy)
  have tele : ∀ n : ℕ, (∏ i ∈ Finset.range n, (D (i + 1) / D i)) = D n / D 0 := by
    intro n
    induction n with
    | zero => simp [div_self (hDne' 0)]
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have h0 := hDne' 0
      have hn := hDne' n
      field_simp
  -- rewrite the `Fin r` product as a `range r` product of `D` ratios
  have e1 : (∏ j : Fin r, pivotSq s j) = ∏ i ∈ Finset.range r, (D (i + 1) / D i) := by
    rw [Finset.prod_fin_eq_prod_range]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hir : i < r := Finset.mem_range.mp hi
    have hi1 : i + 1 ≤ r := hir
    have hi0 : i ≤ r := le_of_lt hir
    rw [dif_pos hir, hDk (i + 1) hi1, hDk i hi0]
    rfl
  -- conjunct 1: the pivots multiply to the squared volume
  have h1 : (∏ j : Fin r, pivotSq s j) = S.det ^ 2 := by
    have e3 : D r / D 0 = S.det ^ 2 := by
      rw [hDk r le_rfl, hDk 0 (Nat.zero_le r), hD0, div_one, hDr]
    rw [e1, tele r, e3]
  -- conjunct 2: the dichotomy is classical logic
  have h2 : (∀ j : Fin r, κ ^ 2 ≤ pivotSq s j) ∨ (∃ j : Fin r, pivotSq s j < κ ^ 2) := by
    by_cases h : ∀ j : Fin r, κ ^ 2 ≤ pivotSq s j
    · exact Or.inl h
    · obtain ⟨j, hj⟩ := not_forall.mp h
      exact Or.inr ⟨j, lt_of_not_ge hj⟩
  -- conjunct 3: broad pivots give the volume lower bound
  have h3 : (∀ j : Fin r, κ ^ 2 ≤ pivotSq s j) → κ ^ (2 * r) ≤ S.det ^ 2 := by
    intro hall
    have e2 : (∏ _j : Fin r, κ ^ 2) = κ ^ (2 * r) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [← e2, ← h1]
    exact Finset.prod_le_prod (fun j _ => sq_nonneg κ) (fun j _ => hall j)
  exact ⟨h1, h2, h3⟩

end FilteredDescent
