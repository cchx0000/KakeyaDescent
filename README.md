# Filtered Descent for the Physical Kakeya Incidence — Lean Formalization

Formalization of the filtered descent argument for the physical Kakeya
incidence bound (paper: `paper.pdf`).

## Status

**This is a work in progress, not a complete kernel-verified formalization
of the paper.** See "Known gaps" below.

### What is proved

- **Descent machinery** (abstract lemmas, all with real Lean proofs):
  - `SubpowerLE` and its algebra (`Def_FilteredDescent_Subpower`)
  - Packet law, marginal law, tree leaves, Gram take (`Def_FilteredDescent_Packet`, etc.)
  - R5 marginal bound (`Thm_FilteredDescent_R5`)
  - Duplicate closure / kernel chain confluence (`Thm_FilteredDescent_DuplicateClosure`, `Thm_FilteredDescent_KernelChain`)
  - Pivot dichotomy, tree LCA reduction (`Thm_FilteredDescent_PivotDichotomy`, `Thm_FilteredDescent_TreeLCA`)
  - Root-cross gate (M7) (`Thm_FilteredDescent_RootCrossGate`)
  - Support recurrence closure, terminal incidence count (`Thm_FilteredDescent_SupportRecurrence`, `Thm_FilteredDescent_TerminalCount`)
  - Ordered Cauchy-Binet (`Thm_FilteredDescent_OrderedCauchyBinet`, modulo the axiom below)

- **Scalar closure** (`Thm_FilteredDescent_ScalarClosure`):
  - d=2, d=3, d=4: **proved** (zero `sorry`) from the pair-incidence input
    + single-tube bound, via the descent machinery (root-cross gate) +
    the algebraic lemma `sum_le_of_pair_bound`.
    The multiplicity bound `M ≲ 1` is **derived**, not assumed.
    The d=2 case uses `PlanarInput` (now in geometric pair-incidence form,
    parallel to d=3,4) via `planarInput_to_Hgeom`.

### External dependencies (axioms)

- `ClassicalGaps.cauchy_binet_det`: imported as an `axiom` from the
  Prove2Me formalpedia (status: Proved there). Not proved locally.

### Known gaps

1. **No real Kakeya geometry.** `ShadedTubes` is an abstract interface:
   three real functions (`shadeVol`, `unionVol`, `multiplicity`) with
   algebraic relations (including `shade_le_union`: each tube's shaded
   volume ≤ union volume). There are no tubes, direction separation,
   Lebesgue measure, or sticky maps. What Lean verifies are the algebraic
   consequences of the abstract inputs, not the geometric theorem.

2. **Trivial tree.** The descent is instantiated on a star tree
   (root + n leaves). The paper uses a real multi-scale tree built from
   tube geometry. With the trivial tree, the descent machinery is
   correctly formalized but vacuous: `Xroot` is just the input pair sum.

3. **Descent chain not fully linked.** The modules R5, DuplicateClosure,
   SupportRecurrence, TerminalCount are proved but `scalar_closure`
   does not yet import/use all of them in a single chain. The current
   d=2,3,4 proof uses RootCrossGate + the algebraic lemma
   `sum_le_of_pair_bound`.

4. **Cauchy–Binet is an axiom.** The determinant identity is imported
   from the Prove2Me formalpedia, not proved locally.

## Building

```bash
cd lean
lake build
```

Requires Lean 4.33.1 and mathlib (pinned commit in `lakefile.lean`).

## Prove2Me

Proposal `a8573c95-0003-4cd8-93c6-9e6670624d32` (Draft, unsubmitted).
The platform draft is stale relative to this repo; sync pending.
