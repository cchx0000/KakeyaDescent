import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

/-!
# Filtered descent — finite packet model (paper (9), (17)–(18), (25))

Finite model of the descent's "packet" picture.  The paper works with
ordered packets of tubes `U = (U_1, …, U_r)` weighted by the product of the
tube weights; R5 ((9)/(25)) says that after retaining an event of mass `α`,
each slot's marginal is dominated by `α⁻¹` times the base law.
-/

namespace FilteredDescent

/-- Finite symmetric packet law (paper (17)): on ordered `r`-tuples of tubes,
the product weight normalized by the total mass `W^r`. -/
noncomputable def packetLaw {n r : ℕ} (w : Fin n → ℝ) : (Fin r → Fin n) → ℝ :=
  fun U => (∏ j, w (U j)) / (∑ i, w i) ^ r

/-- One-slot marginal mass: total packet mass of tuples with `U j = t`.
Paper (18): before conditioning this equals the coarse shaded-incidence
marginal `w t / W`. -/
noncomputable def slotMarginal {n r : ℕ} (w : Fin n → ℝ) (j : Fin r)
    (t : Fin n) : ℝ :=
  ∑ U : Fin r → Fin n, if U j = t then packetLaw w U else 0

/-- Retained packet mass of an event `A` under the packet law.  This is the
finite form of the retained mass `α` in R5 (paper (9)/(25)). -/
noncomputable def retainedMass {n r : ℕ} (w : Fin n → ℝ)
    (A : Finset (Fin r → Fin n)) : ℝ :=
  ∑ U ∈ A, packetLaw w U

end FilteredDescent
