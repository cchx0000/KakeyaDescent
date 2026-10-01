# Blind read-back: `FilteredDescent_SubpowerLE`

File: `Definitions/Def_FilteredDescent_Subpower.lean`
Namespace: `FilteredDescent`. Imports: `Mathlib.Analysis.SpecialFunctions.Pow.Real`, `Mathlib.Data.Real.Basic`.
No `sorry` / `axiom` in the file; both theorems carry complete tactic proofs.

## Definitions

**`def SubpowerLE (x y : ℝ → ℝ) : Prop`**

Compares *functions* of a scale parameter `δ`, not scalar reals at a fixed `δ`:

```
SubpowerLE x y := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
  ∀ δ : ℝ, 0 < δ → δ < 1 → x δ ≤ C * δ ^ (-ε) * y δ
```

Quantifier order is `∀ ε, ∃ C, ∀ δ ∈ (0,1)`: the constant `C` is chosen
before `δ` is quantified, so as written `C` may depend on `ε` (and on `x`,
`y`) but **cannot depend on `δ`**. This is a uniform-in-`δ` family-level
bound, matching the doc comment's claim ("allowed to depend on `ε` …
but *not* on `δ`").

No nonnegativity of `x` or `y` is built into the definition. Since
`δ ^ (-ε) > 0` for `δ > 0`, if `y δ < 0` somewhere then
`C * δ ^ (-ε) * y δ ≤ 0`, forcing `x δ ≤ 0` there. The zero function is
subpower-bounded by everything (take `C = 0`).

## Theorems (both fully proved)

**`theorem SubpowerLE.refl {x : ℝ → ℝ} (hx : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ x δ) : SubpowerLE x x`**

Reflexivity, but only under the explicit hypothesis that `x` is
nonnegative on `(0,1)`. Proof uses `C = 1` and `δ ^ (-ε) ≥ 1` for
`δ ∈ (0,1)`, `ε > 0`.

**`theorem SubpowerLE.trans_right {x y z : ℝ → ℝ} (hxy : SubpowerLE x y) (hyz : SubpowerLE y z) : SubpowerLE x z`**

Right-transitivity. Proof splits `ε` as `ε/2 + ε/2`, multiplies the
constants (`C₁ * C₂`, nonnegative), and uses `δ ^ (-ε) = δ ^ (-ε/2) *
δ ^ (-ε/2)` via `Real.rpow_add`. No sign hypotheses needed because the
multiplier `C₁ * δ ^ (-ε/2)` is shown nonnegative before chaining.

## Notes

- The definition is genuinely uniform in `δ` by quantifier order; it is
  *not* the weaker per-`δ` formulation `∀ δ, ∀ ε, ∃ C, ...`.
- `refl` is not unconditional: it needs `0 ≤ x` on `(0,1)`. This is a
  real hypothesis, not a formality.
- `trans_right` is right-composition only (`x ≲ y ≲ z ⇒ x ≲ z`); there is
  no left-transitivity or monotonicity lemma in this file.
