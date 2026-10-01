import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Filtered descent — Gram–Schmidt pivots (paper (32)–(42))

The Gram–Schmidt pivot decomposition of the ordered Cauchy–Binet identity.
For an ordered `r`-tuple of vectors, `p_j^2 = det G_j / det G_{j-1}` is the
squared distance of the `j`-th vector to the span of the previous ones
(paper (32)–(33)), and `|det S| = ∏_j p_j` (paper (36)–(42)).
-/

namespace FilteredDescent

/-- Gram matrix of the leading `k`-subfamily of `s` (embedded as `k × k`). -/
noncomputable def gramTake {r d : ℕ} (s : Fin r → (Fin d → ℝ)) (k : ℕ)
    (hk : k ≤ r) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of (fun i j =>
    ∑ a, s ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ a * s ⟨j.val, lt_of_lt_of_le j.isLt hk⟩ a)

/-- Gram–Schmidt pivot (paper (32)–(33)):
`p_j^2 = det G_{j+1} / det G_j`, the squared distance of `s_j` to the span of
the previous vectors.  Positivity of the Gram determinants is a hypothesis
of the pivot dichotomy theorem, not of this definition. -/
noncomputable def pivotSq {r d : ℕ} (s : Fin r → (Fin d → ℝ)) (j : Fin r) : ℝ :=
  (gramTake s (j.val + 1) (Nat.succ_le_of_lt j.isLt)).det /
    (gramTake s j.val (le_of_lt j.isLt)).det

end FilteredDescent
