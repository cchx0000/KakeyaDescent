import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

namespace FilteredDescent

/-- Subpower-loss domination `x ≲ y` uniformly for `δ ∈ (0,1)` (paper's `≲ δ^{-o(1)}`).

  For every `ε > 0` there is a constant `C ≥ 0` — allowed to depend on `ε`
  and on the dimension, but *not* on `δ` — such that
  `x δ ≤ C * δ ^ (-ε) * y δ` for *all* `δ ∈ (0,1)`.
  The paper uses this pervasively to bookkeep subpower losses as `δ → 0`.
  Quantities compared here are functions of the scale `δ`; constant
  quantities are embedded via `fun _ => c`. -/
def SubpowerLE (x y : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → x δ ≤ C * δ ^ (-ε) * y δ

/-- Subpower domination is reflexive on quantities nonnegative on `(0,1)`. -/
theorem SubpowerLE.refl {x : ℝ → ℝ} (hx : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ x δ) :
    SubpowerLE x x := by
  unfold SubpowerLE
  intro ε hε
  refine ⟨1, zero_le_one, fun δ hδ0 hδ1 => ?_⟩
  have h : (1 : ℝ) ≤ δ ^ (-ε) := by
    rw [Real.rpow_neg (le_of_lt hδ0)]
    exact (one_le_inv_iff₀).mpr ⟨Real.rpow_pos_of_pos hδ0 ε,
      le_of_lt (Real.rpow_lt_one (le_of_lt hδ0) hδ1 hε)⟩
  calc x δ = 1 * x δ := by ring
    _ ≤ δ ^ (-ε) * x δ := mul_le_mul_of_nonneg_right h (hx δ hδ0 hδ1)
    _ = 1 * δ ^ (-ε) * x δ := by ring

/-- Chaining a subpower bound through a middle factor. -/
theorem SubpowerLE.trans_right {x y z : ℝ → ℝ}
    (hxy : SubpowerLE x y) (hyz : SubpowerLE y z) :
    SubpowerLE x z := by
  unfold SubpowerLE at *
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := hxy (ε / 2) (by linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := hyz (ε / 2) (by linarith)
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, fun δ hδ0 hδ1 => ?_⟩
  have hpow : δ ^ (-ε) = δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) := by
    rw [← Real.rpow_add hδ0]
    ring_nf
  have hnn : 0 ≤ δ ^ (-(ε / 2)) := Real.rpow_nonneg (le_of_lt hδ0) _
  calc x δ ≤ C₁ * δ ^ (-(ε / 2)) * y δ := h₁ δ hδ0 hδ1
    _ ≤ C₁ * δ ^ (-(ε / 2)) * (C₂ * δ ^ (-(ε / 2)) * z δ) :=
        mul_le_mul_of_nonneg_left (h₂ δ hδ0 hδ1) (mul_nonneg hC₁ hnn)
    _ = (C₁ * C₂) * δ ^ (-ε) * z δ := by rw [hpow]; ring

/-- Subpower domination respects sums (general form, possibly different
right-hand sides).  This subsumes the old same-`y` special case. -/
theorem SubpowerLE.add {x₁ x₂ y₁ y₂ : ℝ → ℝ}
    (h₁ : SubpowerLE x₁ y₁) (h₂ : SubpowerLE x₂ y₂)
    (hy₁ : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ y₁ δ)
    (hy₂ : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ y₂ δ) :
    SubpowerLE (fun δ => x₁ δ + x₂ δ) (fun δ => y₁ δ + y₂ δ) := by
  intro ε hε
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁ ε hε
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂ ε hε
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun δ hδ0 hδ1 => ?_⟩
  have h1 := hb₁ δ hδ0 hδ1
  have h2 := hb₂ δ hδ0 hδ1
  have hy1 := hy₁ δ hδ0 hδ1
  have hy2 := hy₂ δ hδ0 hδ1
  have hpow : 0 ≤ δ ^ (-ε) := le_of_lt (Real.rpow_pos_of_pos hδ0 _)
  calc x₁ δ + x₂ δ
      ≤ (C₁ * δ ^ (-ε) * y₁ δ) + (C₂ * δ ^ (-ε) * y₂ δ) :=
        add_le_add h1 h2
    _ ≤ (C₁ + C₂) * δ ^ (-ε) * (y₁ δ + y₂ δ) := by
        have e : (C₁ + C₂) * δ ^ (-ε) * (y₁ δ + y₂ δ)
            - ((C₁ * δ ^ (-ε) * y₁ δ) + (C₂ * δ ^ (-ε) * y₂ δ))
            = C₁ * δ ^ (-ε) * y₂ δ + C₂ * δ ^ (-ε) * y₁ δ := by ring
        linarith [mul_nonneg (mul_nonneg hC₁ hpow) hy2,
          mul_nonneg (mul_nonneg hC₂ hpow) hy1]

/-- Absorb a doubled bound into the subpower constant. -/
theorem SubpowerLE.of_double {x y : ℝ → ℝ}
    (h : SubpowerLE x (fun δ => y δ + y δ)) : SubpowerLE x y := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨2 * C, by linarith, fun δ hδ0 hδ1 => ?_⟩
  calc x δ ≤ C * δ ^ (-ε) * (y δ + y δ) := hb δ hδ0 hδ1
    _ = (2 * C) * δ ^ (-ε) * y δ := by ring

end FilteredDescent
