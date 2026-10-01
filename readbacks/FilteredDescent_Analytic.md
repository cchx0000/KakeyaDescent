# Blind read-back: Definitions/Def_FilteredDescent_Analytic.lean

Namespace: `FilteredDescent`. Imports: the `Def_FilteredDescent_Subpower`
module, the `Def_FilteredDescent_Tree` module, and two Mathlib modules
(BigOperators Finset, Real). Contains no theorems.

## `PlanarInput`
`def PlanarInput (Kpr : ℝ → ℝ) : Prop := SubpowerLE Kpr (fun _ => 1)`
- `Kpr` explicit. Applies the imported constant `SubpowerLE` to the two
  functions `Kpr` and the constant function `1`.

## `StickyInput`
`def StickyInput {n : ℕ} (shadeVol : Fin n → ℝ → ℝ) (unionVol multiplicity : ℝ → ℝ) : Prop :=`
`  SubpowerLE (fun _ => 1) (fun δ => unionVol δ / ∑ t, shadeVol t δ) ∧`
`  SubpowerLE multiplicity (fun _ => 1)`
- `n` implicit; the three function arguments explicit.
- A conjunction: (1) `SubpowerLE` of the constant-`1` function against
  `fun δ => unionVol δ / ∑ t, shadeVol t δ`; (2) `SubpowerLE` of
  `multiplicity` against the constant-`1` function.

## `Marked4DInput`
Byte-for-byte identical signature and body to `StickyInput`: same
implicit `{n : ℕ}`, same argument names/types, same conjunction of the
same two `SubpowerLE` statements. Two names, one proposition.

## `ShadedTubes`
`structure ShadedTubes (n : ℕ)` — `n` explicit.
- Data: `shadeVol : Fin n → ℝ → ℝ`, `unionVol : ℝ → ℝ`,
  `multiplicity : ℝ → ℝ`.
- Proof fields (each premises `0 < δ`, `δ < 1`):
  - `shade_nonneg : ∀ t δ, 0 < δ → δ < 1 → 0 ≤ shadeVol t δ`
  - `union_nonneg : ∀ δ, 0 < δ → δ < 1 → 0 ≤ unionVol δ`
  - `mult_pos : ∀ δ, 0 < δ → δ < 1 → 0 < multiplicity δ`
  - `mult_eq : ∀ δ, 0 < δ → δ < 1 → multiplicity δ * unionVol δ = ∑ t, shadeVol t δ`

## `GateStage`
`structure GateStage (α : Type) [DecidableEq α] (n m : ℕ)` — `α`
explicit, `DecidableEq α` instance-implicit, `n m` explicit.
- `tree : Finset (List α)`; `hroot : [] ∈ tree`;
  `hprefix : ∀ l ∈ tree, ∀ p : List α, p <+: l → p ∈ tree` (prefix-closed).
- `load : List α → ℝ → ℝ`;
  `hload : ∀ γ ∈ treeLeaves tree, ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ load γ δ`.
  Nonnegativity is required only on `treeLeaves tree` (an imported
  constant), though `load` is total on `List α`.
- `termTube : List α → Fin n`, `carrier : List α → Fin m` — both total
  on `List α`; no requirement that the argument lies in `tree`.
- `shadeVol`, `unionVol`, `multiplicity` plus the four
  `ShadedTubes`-shaped proof fields
  (`shade_nonneg`, `union_nonneg`, `mult_pos`, `mult_eq`).
- `Bpred : ℝ → ℝ`;
  `Bpred_nonneg : ∀ δ, 0 < δ → δ < 1 → 0 ≤ Bpred δ`.

## Surprising / disconnected (code-literal)
1. `StickyInput` and `Marked4DInput` are the same proposition under two names.
2. In `GateStage` nothing relates the tree/load/labeling part to the
   analytic part: `termTube` maps histories to tube indices, but no field
   connects `load γ δ` with `shadeVol (termTube γ) δ`, and `mult_eq`
   mentions neither `tree`, `load`, `termTube`, nor `carrier`.
3. `carrier` (hence `m`) occurs in no other field or hypothesis.
4. `Bpred` occurs in no other field or hypothesis beyond its own nonnegativity.
5. `mult_eq` forces `multiplicity δ * unionVol δ = ∑ t, shadeVol t δ`
   while `unionVol δ` is only required `≥ 0`, so the equation can hold
   with `unionVol δ = 0`, `∑ shadeVol = 0`, and `multiplicity δ > 0`.
6. `hload` constrains `load` only on leaves; nothing constrains `load`
   off `treeLeaves tree`.
7. `SubpowerLE` is applied throughout to `ℝ → ℝ` functions (two
   arguments); its quantifier structure is defined in the imported
   module, not in this file.
