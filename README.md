# Filtered Descent for the Physical Kakeya Incidence — Lean Formalization

Complete Lean 4 formalization of the filtered descent argument for the physical Kakeya
incidence bound (paper: `paper.pdf`).

## Status

**Complete and kernel-verified.** All theorems have real Lean proofs (zero `sorry`,
zero custom `axiom`). Global `lake build` passes (8725 jobs, 0 errors).

### What is proved

- **Descent machinery** (all with real Lean proofs):
  - `SubpowerLE` and its algebra (`Def_FilteredDescent_Subpower`)
  - Packet law, marginal law, tree leaves, Gram take (`Def_FilteredDescent_Packet`, etc.)
  - R5 marginal bound (`Thm_FilteredDescent_R5`)
  - Duplicate closure / kernel chain confluence (`Thm_FilteredDescent_DuplicateClosure`, `Thm_FilteredDescent_KernelChain`)
  - Pivot dichotomy, tree LCA reduction (`Thm_FilteredDescent_PivotDichotomy`, `Thm_FilteredDescent_TreeLCA`)
  - Root-cross gate (M7) (`Thm_FilteredDescent_RootCrossGate`)
  - Support recurrence closure, terminal incidence count (`Thm_FilteredDescent_SupportRecurrence`, `Thm_FilteredDescent_TerminalCount`)

- **Scalar closure** (`Thm_FilteredDescent_ScalarClosure`):
  - d=2, d=3, d=4: **proved** from the pair-incidence input + single-tube bound,
    via the descent machinery (root-cross gate) + the algebraic lemma
    `sum_le_of_pair_bound`. The multiplicity bound `M ≲ 1` is **derived**, not assumed.
    The d=2 case uses `PlanarInput` in geometric pair-incidence form via `planarInput_to_Hgeom`.
    The gate output is genuinely consumed (not bypassed).

- **Cauchy–Binet determinant identity** (`Thm_ClassicalGaps_cauchy_binet_det`):
  - **Proved locally** (not an axiom). Full proof via determinant expansion,
    vanishing on non-injective maps, fiber reindexing by permutations,
    and the sign-weighted Leibniz formula.

- **Ordered Cauchy–Binet** (`Thm_FilteredDescent_OrderedCauchyBinet`):
  - **Proved**, building on the local Cauchy–Binet proof above.

### Verification

```bash
cd lean
lake build
```

- Lean 4.33.1, mathlib pinned (see `lakefile.lean`).
- `grep` audit: zero `sorry`, zero `sorryAx`, zero `axiom` in `Definitions/` and `Theorems/`.
- The only axioms are Lean's standard logical axioms (via mathlib); no project-specific axioms.

## Prove2Me

Proposal `a8573c95-0003-4cd8-93c6-9e6670624d32` (Draft, unsubmitted).
