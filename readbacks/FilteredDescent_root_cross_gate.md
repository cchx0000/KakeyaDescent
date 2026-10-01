# Blind read-back: `FilteredDescent.root_cross_gate`

File: `Theorems/Thm_FilteredDescent_RootCrossGate.lean`.
Imports: `Definitions.Def_FilteredDescent_Analytic` and three mathlib modules
(BigOperators, Fintype, Real). `PlanarInput`, `StickyInput`,
`Marked4DInput`, `GateStage`, `Xdup`, `Xroot`, `treeLeaves`, `SubpowerLE`
all come from the import; none are defined here.

## Signature

```lean
theorem root_cross_gate {α : Type} [DecidableEq α] {n m : ℕ}
    (d : ℕ) (hd : d = 2 ∨ d = 3 ∨ d = 4)
    (G : GateStage α n m)
    (Kpr : ℝ → ℝ) (H2 : d = 2 → PlanarInput Kpr)
    (H3 : d = 3 → StickyInput G.shadeVol G.unionVol G.multiplicity)
    (H4 : d = 4 → Marked4DInput G.shadeVol G.unionVol G.multiplicity)
    (Hdup :
      SubpowerLE (fun δ => Xdup G.tree (fun γ => G.load γ δ) G.termTube)
        (fun δ => G.Bpred δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ)) :
    SubpowerLE (fun δ => Xroot G.tree (fun γ => G.load γ δ))
      (fun δ => G.Bpred δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ) := by
  sorry
```

## Conclusion

`SubpowerLE` applied to the pair of functions
`fun δ => Xroot G.tree (fun γ => G.load γ δ)` and
`fun δ => G.Bpred δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ`.
The proof is `by sorry`; the theorem is unproved.

## Literal observations

1. The RHS bound `G.Bpred δ * ∑ γ ∈ treeLeaves G.tree, G.load γ δ` is
   identical in `Hdup` and in the conclusion. Only the LHS changes: from
   `Xdup G.tree (fun γ => G.load γ δ) G.termTube` to
   `Xroot G.tree (fun γ => G.load γ δ)`.
2. `H2`, `H3`, `H4` are implication-shaped (`d = k → ...`), so at most one
   can fire given `hd` — but all three are still assumed unconditionally
   as theorem arguments.
3. `Kpr` occurs nowhere else in the statement: not in the conclusion, not
   in `Hdup`, not in any other hypothesis. The `d = 2` input is about a
   function `ℝ → ℝ` entirely disconnected from every other term.
4. No hypothesis relates `Xroot` to `Xdup` (no stated decomposition), and
   no hypothesis bounds any separate "geometric" quantity. `Hdup` bounds
   only the `Xdup` term.
5. The conclusion mentions only `G.tree`, `G.load`, `G.Bpred`. It does not
   mention `d`, `n`, `m`, `α`, `G.termTube`, `G.shadeVol`, `G.unionVol`,
   `G.multiplicity`, or `Kpr`.
6. `Xdup` takes three arguments (tree, load function, `G.termTube`);
   `Xroot` takes two (tree, load function).
7. The module doc comment claims the bound is "uniformly for δ ∈ (0,1)".
   This file does not show what `SubpowerLE` quantifies over δ, so the
   uniformity claim is not verifiable from this file alone.
