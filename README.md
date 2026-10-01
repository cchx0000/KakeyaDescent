# Filtered Descent for the Physical Kakeya Incidence — Lean Formalization

Lean 4 formalization (in progress) of the filtered descent argument for the physical Kakeya
incidence bound (paper: `paper/paper.pdf`).

## Status

**Work in progress — not complete.** All committed theorems have real Lean proofs (zero `sorry`,
zero custom `axiom` in `Definitions/` and `Theorems/`); global `lake build` passes (8738 jobs,
0 errors, 0 warnings); `#print axioms` on all top theorems shows only Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). But the formalization is **not** a
complete rendering of the paper yet. What changed recently, and what remains:

**Now proved (this integration):**
- `Hpred` (138), the predecessor invariance, is no longer a hypothesis: `descent_bound`
  (`Thm_FilteredDescent_DescentInduction.lean`) proves it by well-founded induction on the
  descent labels (135) (`DescentLt`, `Thm_FilteredDescent_DescentLabels.lean`), running the
  gate on re-rooted subtrees (`Thm_FilteredDescent_SubtreeReroot.lean`).
- The end-to-end scalar closure is now `Hpred`-free: `scalar_closure_discharged`
  (`Thm_FilteredDescent_EndToEnd.lean`) composes the discharged faithful gate
  (`faithful_gate_discharged`) with the (136)+(145) bridge and the (142)→(214) division,
  and `scalar_closure_discharged_physical` runs it on the real physical tube model
  (`physicalRealization`). The old `scalar_closure` (simplified `root_cross_gate` path)
  is still true but marked superseded in its docstring.
- The duplicate `SubpowerLE.add` is fixed: one general version lives in
  `Def_FilteredDescent_Subpower.lean`; the old same-`y` special case in
  `RootCrossGate.lean` is deleted and its use site goes through `SubpowerLE.of_double`.

**Remaining named hypotheses** (explicit, not proved — see `MAPPING.md` and the module
docstring of `Thm_FilteredDescent_EndToEnd.lean`):
- `DescentLabels T lab`: the §§6–9 history-tree construction (support faces, confluence
  type, Cartan height) with the (135) label-decrease property.
- `leaf_bound`: the pointwise leaf estimate, paper (53) at the minimal label.
- `terminal_hardening : ∀ x ∈ T, …`: the R5 terminal bound (148) on every re-rooted
  subtree (the (θ,j,c) model data is root-only; per-subtree threading is future work).
- `geom_pair : ∀ x ∈ T, …`: the geometric pair estimate ((53)/(177)/(81) shape) on every
  re-rooted subtree (root instance from the d=2/3/4 inputs via `faithful_geom_pair`).
- `htotalLoad`: the (136)+(145) bridge from tree loads to tube-family shading.

**Other known gaps:**
- `duplicate_closure` (old) still proves an abstract carrier bound, not the paper's exact
  identity (146); the exact (146)/(147) identities live in the faithful-gate files and are
  the ones consumed in-chain.
- Kernel chain, pivot dichotomy, support recurrence are proved standalone, not yet
  connected into the main chain (R5 is connected via `terminal_hardening`).
- The typed Hall-capacity route (160)/(207) is explicitly excluded (see `MAPPING.md`).
- The deep geometric estimates [2] (planar Córdoba), [7,10] (sticky), [9] (marked 4D)
  enter only as named hypotheses; d ≥ 5 is unclaimed.

Do not cite this repository as a complete formalization of the paper.

### What is proved

- **Descent machinery** (all with real Lean proofs):
  - `SubpowerLE` and its algebra, incl. the general `SubpowerLE.add` and
    `SubpowerLE.of_double` (`Def_FilteredDescent_Subpower`)
  - Packet law, marginal law, tree leaves, Gram take (`Def_FilteredDescent_Packet`, etc.)
  - R5 marginal bound (`Thm_FilteredDescent_R5`)
  - Duplicate closure / kernel chain confluence (`Thm_FilteredDescent_DuplicateClosure`, `Thm_FilteredDescent_KernelChain`)
  - Pivot dichotomy, tree LCA reduction (`Thm_FilteredDescent_PivotDichotomy`, `Thm_FilteredDescent_TreeLCA`)
  - Root-cross gate (M7) (`Thm_FilteredDescent_RootCrossGate`)
  - Support recurrence closure, terminal incidence count (`Thm_FilteredDescent_SupportRecurrence`, `Thm_FilteredDescent_TerminalCount`)

- **Faithful §10 gate** (`Thm_FilteredDescent_FaithfulGate*.lean`, all with real proofs):
  - (139)/(141) proper-predecessor recombination (`proper_predecessor_bound`)
  - (144) `Xroot = Xgeom + Xdup` split, (146) exact duplicate identity (`xdup_eq`),
    (147) geometric control (`xgeom_le_offdiag`), (148) terminal hardening via R5
  - `faithful_gate_wired`: the (141)+(142) gate `N(δ)² ≲ B^pred(δ)·N(δ)` from the
    (θ,j,c) model data + pointwise `Hpred` + `geom_pair`
  - `descent_step_subpower` / `descent_proper_subpower`: the gate with `Hpred` in
    subpower form (the form the induction closes on)

- **Descent induction** (`Thm_FilteredDescent_DescentLabels/SubtreeReroot/DescentInduction.lean`):
  - (135) well-founded lexicographic order on `(|I|, ℓ(χ), n)` — real proof
  - `descent_bound`: `Hpred` (138) **proved** by well-founded induction
  - `faithful_gate_discharged`: the faithful gate with `Hpred` discharged

- **Scalar closure**:
  - NEW (faithful, `Hpred`-free): `scalar_closure_discharged` and
    `scalar_closure_discharged_physical` (`Thm_FilteredDescent_EndToEnd.lean`) —
    same conclusion `SubpowerLE (∑ t, shadeVol t) unionVol` for d = 2, 3, 4, via the
    discharged faithful gate; the physical version runs on `physicalRealization`.
  - `scalar_closure_faithful` / `scalar_closure_physical`
    (`Thm_FilteredDescent_ScalarFaithful.lean`) — via `faithful_gate_wired`
    (pointwise-`Hpred` + root model data version).
  - OLD (`Thm_FilteredDescent_ScalarClosure`): d=2, 3, 4 proved via the simplified
    root-cross gate + retained-fraction detour — still true, marked superseded.

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
- `#print axioms` audit on the top-level theorems (`scalar_closure_discharged`,
  `scalar_closure_discharged_physical`, `scalar_closure_faithful`,
  `scalar_closure_physical`, `descent_bound`, `faithful_gate_discharged`): only
  `[propext, Classical.choice, Quot.sound]` throughout — Lean's standard logical
  axioms (via mathlib); no project-specific axioms.

## Prove2Me

Proposal `a8573c95-0003-4cd8-93c6-9e6670624d32` (Draft, unsubmitted).
