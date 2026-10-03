import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

namespace FilteredDescent

universe u

/-- Subpower-loss domination `x ≲ y` uniformly for `δ ∈ (0,1)` (paper's `≲ δ^{-o(1)}`).

  For every `ε > 0` there is a constant `C ≥ 0` — allowed to depend on `ε`
  and on the dimension, but *not* on `δ` — such that
  `x δ ≤ C * δ ^ (-ε) * y δ` for *all* `δ ∈ (0,1)`.
  The paper uses this pervasively to bookkeep subpower losses as `δ → 0`.
  Quantities compared here are functions of the scale `δ`; constant
  quantities are embedded via `fun _ => c`. -/
def SubpowerLE (x y : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → x δ ≤ C * δ ^ (-ε) * y δ

/-- Uniform subpower domination (TODO_GUIDANCE P0-1).

The constant `C` is quantified *before* the configuration `cfg : Config δ`,
so `C` may depend on `ε` and on fixed paper parameters (e.g. the ambient
dimension) but must NOT depend on the tube count, the concrete tube family,
the history tree, the retained packet subset, or the carrier alphabet.

This blocks the trivial `C = n` proof: when `n = n(δ)` grows with `δ`
(e.g. `n(δ) ≍ δ^{-(d-1)}`), no fixed `C` works.

The configuration type may depend on `δ` (scale-indexed families). -/
def UniformSubpowerLE (Config : ℝ → Type u)
    (X Y : ∀ δ : ℝ, Config δ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ cfg : Config δ, X δ cfg ≤ C * δ ^ (-ε) * Y δ cfg

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

/-- Pointwise bound with a constant lifts to `SubpowerLE`: from
`f δ ≤ K * g δ` on `(0,1)` with `K ≥ 0` and `g ≥ 0`, take `C = K` and use
`δ ^ (-ε) ≥ 1`. -/
theorem SubpowerLE.of_le_const {f g : ℝ → ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (hf : ∀ δ : ℝ, 0 < δ → δ < 1 → f δ ≤ K * g δ)
    (hg : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ g δ) :
    SubpowerLE f g := by
  intro ε hε
  refine ⟨K, hK, fun δ hδ0 hδ1 => ?_⟩
  have hge : 1 ≤ δ ^ (-ε) := by
    have h1 : δ ^ ε ≤ 1 := Real.rpow_le_one hδ0.le hδ1.le hε.le
    have h2 : (0:ℝ) < δ ^ ε := Real.rpow_pos_of_pos hδ0 ε
    rw [Real.rpow_neg hδ0.le]
    exact (one_le_inv_iff₀).mpr ⟨h2, h1⟩
  have hfg := hf δ hδ0 hδ1
  have hgδ := hg δ hδ0 hδ1
  calc f δ ≤ K * g δ := hfg
    _ ≤ K * (δ ^ (-ε) * g δ) := by
        apply mul_le_mul_of_nonneg_left _ hK
        calc g δ = 1 * g δ := (one_mul _).symm
          _ ≤ δ ^ (-ε) * g δ := mul_le_mul_of_nonneg_right hge hgδ
    _ = K * δ ^ (-ε) * g δ := by ring

/-- Regression test (TODO_GUIDANCE P0-1 acceptance): the uniform API
blocks the trivial `C = n` proof.

`X δ = 1/δ^2` models a growing configuration; `Y δ = 1`. With `ε = 1`,
uniformity would require `1/δ^2 ≤ C * δ^{-1}`, i.e. `1 ≤ C * δ` for all
`δ ∈ (0,1)` — impossible. A non-uniform `C = 1/δ^2` would work, but `C`
cannot depend on `δ`/the configuration. -/
theorem uniform_not_trivial :
    ¬ UniformSubpowerLE (fun _ : ℝ => Unit)
      (fun δ _ => 1 / δ^2) (fun _ _ => (1 : ℝ)) := by
  intro h
  obtain ⟨C, hC, hbound⟩ := h 1 (by norm_num)
  -- Key: 1/δ^2 ≤ C * δ^{-1} implies 1 ≤ C * δ.
  have key : ∀ δ : ℝ, 0 < δ → δ < 1 → (1:ℝ) ≤ C * δ := by
    intro δ hδ0 hδ1
    have hb := hbound δ hδ0 hδ1 ()
    simp only at hb
    -- hb : 1/δ^2 ≤ C * δ^{-1} * 1
    rw [mul_one] at hb
    -- δ^{-(1:ℝ)} = 1/δ
    have hrpow : δ ^ (-(1:ℝ)) = 1 / δ := by
      rw [Real.rpow_neg (le_of_lt hδ0), Real.rpow_one, inv_eq_one_div]
    rw [hrpow] at hb
    -- Multiply by δ^2 > 0
    have hδ2 : (0:ℝ) < δ^2 := by positivity
    have h1 := mul_le_mul_of_nonneg_right hb (le_of_lt hδ2)
    -- LHS: (1/δ^2) * δ^2 = 1
    rw [div_mul_cancel₀ _ (ne_of_gt hδ2)] at h1
    -- RHS: (C * (1/δ)) * δ^2 = C * δ
    have hδne : δ ≠ 0 := ne_of_gt hδ0
    have h2 : C * (1 / δ) * δ^2 = C * δ := by
      field_simp
    rw [h2] at h1
    exact h1
  -- Take δ = 1/(2*(C+1)): then C*δ = C/(2*(C+1)) < 1.
  have hC1 : (0:ℝ) < C + 1 := by linarith [hC]
  set δ₀ := 1 / (2 * (C+1)) with hδ₀
  have hδ0 : (0:ℝ) < δ₀ := by positivity
  have hδ1 : δ₀ < 1 := by
    rw [hδ₀, div_lt_one (by positivity)]
    linarith [hC]
  have hcon := key δ₀ hδ0 hδ1
  have hlt : C * δ₀ < 1 := by
    rw [hδ₀]
    have hpos : (0:ℝ) < 2 * (C+1) := by positivity
    rw [mul_one_div, div_lt_one hpos]
    linarith [hC]
  linarith [hcon, hlt]

/-- Uniform subpower domination is reflexive on quantities nonnegative on `(0,1)`. -/
theorem UniformSubpowerLE.refl {Config : ℝ → Type u}
    {X : ∀ δ : ℝ, Config δ → ℝ}
    (hx : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ cfg : Config δ, 0 ≤ X δ cfg) :
    UniformSubpowerLE Config X X := by
  unfold UniformSubpowerLE
  intro ε hε
  refine ⟨1, zero_le_one, fun δ hδ0 hδ1 cfg => ?_⟩
  have h : (1 : ℝ) ≤ δ ^ (-ε) := by
    rw [Real.rpow_neg (le_of_lt hδ0)]
    exact (one_le_inv_iff₀).mpr ⟨Real.rpow_pos_of_pos hδ0 ε,
      le_of_lt (Real.rpow_lt_one (le_of_lt hδ0) hδ1 hε)⟩
  calc X δ cfg = 1 * X δ cfg := by ring
    _ ≤ δ ^ (-ε) * X δ cfg := mul_le_mul_of_nonneg_right h (hx δ hδ0 hδ1 cfg)
    _ = 1 * δ ^ (-ε) * X δ cfg := by ring

/-- Chaining a uniform subpower bound through a middle factor. -/
theorem UniformSubpowerLE.trans_right {Config : ℝ → Type u}
    {X Y Z : ∀ δ : ℝ, Config δ → ℝ}
    (hxy : UniformSubpowerLE Config X Y) (hyz : UniformSubpowerLE Config Y Z) :
    UniformSubpowerLE Config X Z := by
  unfold UniformSubpowerLE at *
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := hxy (ε / 2) (by linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := hyz (ε / 2) (by linarith)
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, fun δ hδ0 hδ1 cfg => ?_⟩
  have hpow : δ ^ (-ε) = δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) := by
    rw [← Real.rpow_add hδ0]
    ring_nf
  have hnn : 0 ≤ δ ^ (-(ε / 2)) := Real.rpow_nonneg (le_of_lt hδ0) _
  calc X δ cfg ≤ C₁ * δ ^ (-(ε / 2)) * Y δ cfg := h₁ δ hδ0 hδ1 cfg
    _ ≤ C₁ * δ ^ (-(ε / 2)) * (C₂ * δ ^ (-(ε / 2)) * Z δ cfg) :=
        mul_le_mul_of_nonneg_left (h₂ δ hδ0 hδ1 cfg) (mul_nonneg hC₁ hnn)
    _ = (C₁ * C₂) * δ ^ (-ε) * Z δ cfg := by rw [hpow]; ring

/-- Pointwise uniform bound with a constant lifts to `UniformSubpowerLE`. -/
theorem UniformSubpowerLE.of_le_const {Config : ℝ → Type u}
    {X Y : ∀ δ : ℝ, Config δ → ℝ} {K : ℝ}
    (hK : 0 ≤ K)
    (hf : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ cfg : Config δ, X δ cfg ≤ K * Y δ cfg)
    (hg : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ cfg : Config δ, 0 ≤ Y δ cfg) :
    UniformSubpowerLE Config X Y := by
  intro ε hε
  refine ⟨K, hK, fun δ hδ0 hδ1 cfg => ?_⟩
  have hge : 1 ≤ δ ^ (-ε) := by
    have h1 : δ ^ ε ≤ 1 := Real.rpow_le_one hδ0.le hδ1.le hε.le
    have h2 : (0:ℝ) < δ ^ ε := Real.rpow_pos_of_pos hδ0 ε
    rw [Real.rpow_neg hδ0.le]
    exact (one_le_inv_iff₀).mpr ⟨h2, h1⟩
  have hfg := hf δ hδ0 hδ1 cfg
  have hgδ := hg δ hδ0 hδ1 cfg
  calc X δ cfg ≤ K * Y δ cfg := hfg
    _ ≤ K * (δ ^ (-ε) * Y δ cfg) := by
        apply mul_le_mul_of_nonneg_left _ hK
        calc Y δ cfg = 1 * Y δ cfg := (one_mul _).symm
          _ ≤ δ ^ (-ε) * Y δ cfg := mul_le_mul_of_nonneg_right hge hgδ
    _ = K * δ ^ (-ε) * Y δ cfg := by ring

end FilteredDescent
