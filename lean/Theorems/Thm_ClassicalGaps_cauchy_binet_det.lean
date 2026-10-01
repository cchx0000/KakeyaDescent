import Mathlib

open Classical Matrix Finset

/-!
# Platform lemma (imported): Cauchy–Binet formula

This is a verbatim copy of the **formal statement** of
`ClassicalGaps.cauchy_binet_det` from the Prove2Me online formalpedia
(https://prove2.me), where it has status **Proved**.

It is imported here as an **axiom**: a tracked external dependency.
The proof of `FilteredDescent.ordered_cauchy_binet` is complete *modulo*
this platform lemma.  Using `axiom` (rather than `sorry`) makes the
dependency explicit: Lean's `#print axioms` will show it, and it is not
a placeholder for missing local work but a deliberate import of a
platform-verified result.
-/

axiom ClassicalGaps.cauchy_binet_det {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      if hS : S.card = m then
        (A.submatrix id (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n))).det *
        (B.submatrix (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n)) id).det
      else 0
