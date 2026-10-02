# TODO — Filtered Descent Formalization

This file is the single source of truth for remaining work. It consolidates
the "Remaining named hypotheses" / "Known gaps" from `README.md` and
`MAPPING.md` with the F-series (faithful construction) progress.
Work proceeds top-to-bottom by priority. Each item is checked off only when:
its Lean proof has 0 `sorry`, the global `lake build` passes, and the change
is committed and pushed.

## Conventions (standing)

- Faithful to the paper; no silent simplifications. If a simplification is
  unavoidable, it is marked explicitly in the docstring.
- No `sorry`/`admit`/`axiom` in `Definitions/` or `Theorems/`.
- Every work unit: small enough to finish without interruption, then
  commit + push immediately.
- `main` only after integration + full verification.
- Do not update the Prove2Me Draft until the local work is truly complete;
  final Submit is the user's own click.

## Done (F-series, all 0 sorry, pushed to main)

- [x] F1–F4: faithful history-tree construction — `DescentState`, (135)
  labels, `descentTree` (well-founded recursion), `PacketSelect`,
  `selectedTree`, `markovDelete` ledger, `(θ,j,c)` `ModelData` aggregation,
  per-subtree/per-carrier hardening interfaces.
- [x] F5: `faithfulTree0` (`[]`-rooted) + `scalar_closure_faithful_tree`
  (tree root/prefix/labels discharged into `scalar_closure_discharged`).
- [x] F6: `FaithfulModel` (`load_nonneg`, `mass_conserved`,
  `leaf_geometric`) + `scalar_closure_faithful_full` — the three leaf
  hypotheses (`hload`, `htotalLoad`, `leaf_bound`) discharged from model
  fields.
- [x] F7: `node_hardening_via_streamB`
  (`Thm_FilteredDescent_FaithfulHardening.lean`) — per-node (148) via
  stream B's `terminal_hardening`, with `hDb_nn`/`hD`/`hDb_le`/`∑D=totalLoad`
  proved as lemmas.

## Remaining (from README.md / MAPPING.md, in priority order)

### P1 — Discharge `terminal_hardening` per faithful-tree node
`scalar_closure_faithful_full` still takes `terminal_hardening` as a
hypothesis. F7 proved the per-node shape (`node_hardening_via_streamB`).
Remaining:
- [ ] Thread `HardeningInputs` + `hlink`/`hquant`/`Hpred` through each
  node of `faithfulTree0` (internal nodes via `node_hardening_via_streamB`;
  leaf nodes directly from `leaf_geometric`).
- [ ] Update `scalar_closure_faithful_full` so `terminal_hardening` is
  derived, not assumed. (`geom_pair` stays a named hypothesis — external
  literature [2][7,10][9].)

### P2 — `DescentLabels`: the §§6–9 construction
The history tree with support faces, confluence type, and Cartan height,
with the (135) label-decrease property — currently a named input
(`DescentLabels T lab`), not built from a tube family.
- [ ] Support faces from the packet law.
- [ ] Confluence type per node.
- [ ] Cartan height + (135) decrease along `DescentStep`.

### P3 — Per-subtree `geom_pair`
Root instance exists (d=2/3/4 via `faithful_geom_pair`); subtree versions
are named hypotheses. Thread the geometric pair estimate through
re-rooted subtrees.

### P4 — Connect standalone modules into the main chain
Proved standalone, not yet consumed in-chain:
- [ ] Kernel chain confluence.
- [ ] Pivot dichotomy.
- [ ] Support recurrence.
- [ ] Exact duplicate identity (146) vs old abstract `duplicate_closure`.

### P5 — Update repo docs
- [ ] `README.md`: refresh "Remaining named hypotheses" / "Known gaps"
  to reflect F1–F7 (faithful tree is no longer "trivial"; leaf hypotheses
  discharged; per-node hardening proved).
- [ ] `MAPPING.md`: update (148)–(153) row (per-subtree threading status),
  (136)+(145) row (`htotalLoad` discharged via `FaithfulModel`).

## Explicitly out of scope (per MAPPING.md)

- Typed Hall-capacity route (160)/(207) — excluded from `scalar_closure`.
- d ≥ 5 — unclaimed (paper leaves it open).
- `geom_pair` as a proved estimate — external literature input, stays named.
