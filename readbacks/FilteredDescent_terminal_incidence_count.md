# Blind read-back: FilteredDescent.terminal_incidence_count

## Location
`Theorems/Thm_FilteredDescent_TerminalCount.lean`, inside `namespace FilteredDescent`.
Imports: the `Def_FilteredDescent_Subpower` definitions module plus Mathlib modules for
big operators on finsets, fintype, and real numbers.

## Signature
```lean
theorem terminal_incidence_count {n : ℕ} (hn : 0 < n)
    (shadeVol : Fin n → ℝ → ℝ) (unionVol : ℝ → ℝ)
    (hsh : ∀ t δ, 0 < δ → δ < 1 → 0 ≤ shadeVol t δ)
    (hu : ∀ δ, 0 < δ → δ < 1 → 0 ≤ unionVol δ)
    (α M : ℝ → ℝ)
    (hα : ∀ δ, 0 < δ → δ < 1 → 0 < α δ)
    (hM : ∀ δ, 0 < δ → δ < 1 → 0 < M δ)
    (hαsub : SubpowerLE (fun _ => 1) α)
    (hMsub : SubpowerLE M (fun _ => 1))
    (hcount :
      ∀ δ, 0 < δ → δ < 1 →
        unionVol δ ≥ α δ / (2 * M δ) * ∑ t, shadeVol t δ) :
    SubpowerLE (fun δ => ∑ t, shadeVol t δ) unionVol := by
  sorry
```

## Read-back

- `n` is an implicit natural number; `(hn : 0 < n)` is an explicit hypothesis
  (not otherwise referenced in the statement).
- `shadeVol` maps each `t : Fin n` and each scale `δ : ℝ` to a real number;
  `unionVol`, `α`, `M` are each functions `ℝ → ℝ`.
- `hsh` / `hu`: for all scales `δ` with `0 < δ < 1`, every `shadeVol t δ`
  and `unionVol δ` are nonneg.
- `hα` / `hM`: for all scales `δ` with `0 < δ < 1`, `α δ` and `M δ`
  are strictly positive.
- `hαsub`: `SubpowerLE` applied to the constant function `fun _ => 1`
  and to `α` — i.e. `α` is related to the constant-1 function via
  `SubpowerLE` with the constant function in the first argument position.
- `hMsub`: `SubpowerLE` applied to `M` and to the constant function
  `fun _ => 1` — i.e. `M` is related to the constant-1 function via
  `SubpowerLE` with `M` in the first argument position.
- `hcount`: for all scales `δ` with `0 < δ < 1`,
  `unionVol δ ≥ α δ / (2 * M δ) * ∑ t, shadeVol t δ`,
  where the sum is over `t : Fin n`.
- Conclusion: `SubpowerLE` applied to the function
  `fun δ => ∑ t, shadeVol t δ` (first argument) and to `unionVol`
  (second argument).
- The proof is `sorry`; nothing is proved.

## Notes
- The hypothesis `hn : 0 < n` plays no role in any other hypothesis or the
  conclusion; `Fin n` sums are well-formed regardless.
- The file contains no definitions, only this single theorem.
