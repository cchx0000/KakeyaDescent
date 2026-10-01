# Read-back: `FilteredDescent.support_recurrence_closure`

File: `Theorems/Thm_FilteredDescent_SupportRecurrence.lean`.
Blind code-only read-back; nothing beyond what the code states.

## Verbatim statement

```lean
namespace FilteredDescent

theorem support_recurrence_closure {d : ℕ}
    (B : Finset (Fin d) → ℝ → ℝ)
    (hbase : ∀ I : Finset (Fin d), I.card ≤ 2 → SubpowerLE (B I) (fun _ => 1))
    (hrec :
      ∀ I : Finset (Fin d), 2 < I.card →
        ∃ J : Finset (Fin d), J ⊂ I ∧ SubpowerLE (B I) (B J)) :
    ∀ I : Finset (Fin d), SubpowerLE (B I) (fun _ => 1) := by
  sorry

end FilteredDescent
```

## Literal reading

- Namespace: `FilteredDescent`. Implicit parameter `{d : ℕ}`; all other
  binders are explicit, in the order `B`, `hbase`, `hrec`.
- `B : Finset (Fin d) → ℝ → ℝ` — a family of functions `ℝ → ℝ`, one per
  finite subset `I` of `Fin d`.
- `hbase`: for every `I : Finset (Fin d)`, if `I.card ≤ 2` then
  `SubpowerLE (B I) (fun _ => 1)`, where `fun _ => 1` is the constant-1
  function on `ℝ`.
- `hrec`: for every `I : Finset (Fin d)`, if `2 < I.card` then there exists
  `J : Finset (Fin d)` with `J ⊂ I` (strict subset) such that
  `SubpowerLE (B I) (B J)`.
- Conclusion: for every `I : Finset (Fin d)`,
  `SubpowerLE (B I) (fun _ => 1)`.
- `SubpowerLE` is not defined in this file (it is imported); as used here it
  is applied to two arguments of type `ℝ → ℝ`.
- Proof status: the body is `sorry` — the statement is admitted, not proved.
