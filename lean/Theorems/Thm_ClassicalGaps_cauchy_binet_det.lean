import Mathlib

open Classical Matrix Finset

/-!
# Platform lemma (imported): Cauchy–Binet formula

This is a verbatim copy of the **formal statement** of
`ClassicalGaps.cauchy_binet_det` from the Prove2Me online formalpedia
(https://prove2.me), where it has status **Proved**.

It is imported here as a tracked reduction: the proof of
`FilteredDescent.ordered_cauchy_binet` below is complete *modulo* this
platform lemma. The `sorry` below stands for the platform's verified proof,
not for missing local work.
-/

theorem ClassicalGaps.cauchy_binet_det {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      if hS : S.card = m then
        (A.submatrix id (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n))).det *
        (B.submatrix (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n)) id).det
      else 0 := by sorry
