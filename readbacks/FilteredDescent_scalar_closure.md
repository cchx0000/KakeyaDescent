# Read-back: `FilteredDescent.scalar_closure`

**File:** `lean/Theorems/Thm_FilteredDescent_ScalarClosure.lean`

## Imports / origin of names
- Imports `Definitions.Def_FilteredDescent_Analytic` (plus three mathlib modules).
- `ShadedTubes`, `SubpowerLE`, `PlanarInput`, `StickyInput`, `Marked4DInput`
  are **not defined in this file**; they come from the import.
- The file contains exactly one theorem, proved by `sorry`.

## Theorem signature (verbatim)

```lean
theorem scalar_closure {d n : ℕ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4)
    (hn : 0 < n)
    (S : ShadedTubes n)
    (lamIn : ℝ → ℝ)
    (hlam : ∀ δ, 0 < δ → δ < 1 → 0 < lamIn δ)
    (hlamSub : SubpowerLE (fun _ => 1) lamIn)
    (Kpr : ℝ → ℝ)
    (H2 : d = 2 → PlanarInput Kpr)
    (H3 : d = 3 → StickyInput S.shadeVol S.unionVol S.multiplicity)
    (H4 : d = 4 → Marked4DInput S.shadeVol S.unionVol S.multiplicity) :
    SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol
```

## Hypotheses
1. `hd`: `d` is 2, 3, or 4.
2. `hn`: `n` is positive.
3. `S`: a `ShadedTubes n` structure; the signature uses its projections
   `S.shadeVol`, `S.unionVol`, `S.multiplicity`.
4. `lamIn : ℝ → ℝ` with `hlam`: `lamIn δ > 0` for `δ ∈ (0,1)`,
   and `hlamSub`: `SubpowerLE (fun _ => 1) lamIn` (left argument is the
   constant-1 function; `lamIn` is a function, not a number).
5. `Kpr : ℝ → ℝ` and `H2 : d = 2 → PlanarInput Kpr`.
6. `H3 : d = 3 → StickyInput S.shadeVol S.unionVol S.multiplicity`.
7. `H4 : d = 4 → Marked4DInput S.shadeVol S.unionVol S.multiplicity`.

## Conclusion
`SubpowerLE (fun δ => ∑ t, S.shadeVol t δ) S.unionVol`
— a `SubpowerLE` bound relating the sum of `S.shadeVol t δ` over `t`
to `S.unionVol`.

## Surprising observations
- **The dimension hypothesis selects nothing.** The conclusion does not
  mention `d` at all. `H2`/`H3`/`H4` are implications guarded by
  `d = 2`/`d = 3`/`d = 4`, so all three are assumed simultaneously as
  hypotheses; no case analysis on `d` occurs in the statement.
  `hd` interacts with nothing else in the signature.
- `hn : 0 < n` is not used anywhere else in the signature.
- `S.multiplicity` appears in `H3`/`H4` but not in the conclusion.
- `lamIn`, `hlam`, and `hlamSub` do not appear in the conclusion.
- `Kpr` appears only inside `H2`.
- The doc comment describes dimension-selected analytic inputs and a
  multi-milestone proof strategy, but the formal statement assumes all
  three inputs unconditionally and contains no proof (`sorry`).
