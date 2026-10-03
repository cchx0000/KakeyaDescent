# TODO Guidance — KakeyaDescent

Current audit target: `main` at commit
`8a3d6140517a17aac82936eed7a2fcbddad603dc` (2026-10-03).

This document is the execution guide for the **paper-faithful scalar route**.
It intentionally distinguishes:

- local/fixed-configuration lemmas, where ordinary `SubpowerLE` is useful;
- the authoritative Kakeya statement, where constants must be uniform over
  scale-dependent physical configurations.

The main rule is:

> Do not obtain the authoritative uniform theorem by applying a
> fixed-configuration theorem separately and then choosing its constants
> afterwards. Every constant that survives to the top theorem must already be
> controlled before the physical configuration is quantified.

---

# 0. Current audited status

## Completed and worth keeping

- [x] `UniformSubpowerLE` exists with the correct basic quantifier order:
  `C` is chosen before `cfg : Config δ`.
- [x] `uniform_not_trivial` is a regression showing that a growing
  `δ^{-2}` quantity cannot be hidden by choosing a configuration-dependent
  constant.
- [x] A scale-indexed `PhysicalConfig d δ` type exists.
- [x] `FaithfulModel` is parameterized by the actual `S : ShadedTubes n`;
  the old impossible `∀ S` mass-conservation field is gone.
- [x] A nontrivial `FaithfulModel` inhabitance test exists.
- [x] The faithful root split / duplicate identities, re-rooting, and
  well-founded `Hpred` induction are proved.
- [x] F7 was upgraded to `node_hardening_subpower`: it consumes subpower
  predecessor control rather than pointwise `Hpred`.
- [x] `HardeningLedger`, `hardeningInputsAt`, `NodeHLink`, and
  `NodeHQuant` provide one shared per-tree hardening ledger.
- [x] `scalar_closure_discharged` no longer takes a theorem-valued
  `terminal_hardening : ∀ x, ...` parameter; hardening is produced from
  the ledger inside the descent.
- [x] Dimension-indexed `GeomInput` exists and
  `geom_pair_of_geomInput` proves the algebraic conversion once the
  correct subtree source-compatibility data are supplied.
- [x] `PacketSource` derives child mass from the packet law via
  `derivedChildMass` / `packetSelectOfSource`.
- [x] `derivedChildMass_sum` proves the one-step packet-mass fiber identity.
- [x] Paper-faithful `pathMass` and `pathMass_partition` formalize the
  child-cylinder partition behind paper (133).
- [x] The self-invented representative-leaf `SourceModel` layer was removed.
- [x] The symmetric toy `scalar_closure_constructed` theorem was removed.

## Kernel/source hygiene at this audit

Across the current 44 Lean files:

- no project custom `axiom`, `constant`, `opaque`, `extern`, or
  `implemented_by` was found;
- no `admit` / `sorryAx` was found;
- **one real `sorry` remains**, in
  `Thm_FilteredDescent_UniformScalar.lean`, theorem
  `scalar_closure_uniform`.

Therefore the README sentence claiming zero `sorry` is currently stale.

---

# P0 — Make the authoritative uniform theorem actually true

## 1. Do not prove uniformity by post-processing local `SubpowerLE`

The authoritative theorem currently has the right outer target:

```lean
UniformSubpowerLE (UniformScalarConfig d α) X Y
```

but every configuration contains local fixed-family data whose
`SubpowerLE` witnesses may have unrelated constants.

The current `sorry` in `scalar_closure_uniform` is therefore not a tactic
gap. It is a **uniformity/specification gap**.

In particular, the fixed-configuration proof may introduce constants from:

- the geometric pair estimate;
- `HardeningLedger.hcard`;
- `1 / c₀`;
- the finite maximum in `uniform_proper_const`;
- the tree height
  `T.sup' ... List.length + 1`;
- any finite alphabet / branching data fixed before local `SubpowerLE`
  chooses its witness.

### Target

Introduce global assumptions/certificates whose constants are chosen before
the varying configuration. For example, conceptually:

```lean
UniformGeomInput d
UniformHardeningBudget d
UniformDescentComplexity d
```

or one combined `UniformDescentAssumptions d`.

The exact API can differ. The essential point is that these are statements
over **all admissible configurations**, not fields carrying unrelated local
`SubpowerLE` proofs inside each configuration.

### Acceptance test

`scalar_closure_uniform` is proved with no `sorry`, and its proof never
extracts a fixed-configuration `SubpowerLE` constant and then tries to take
a maximum over all configurations.

---

## 2. Uniformize the geometric input itself

Current `GeomInput d S.shadeVol S.unionVol` is dimension-indexed, which is
good, but its payload is still a **local** `SubpowerLE` for one fixed finite
family.

That local statement is not enough for the uniform theorem.

### Target

Add a genuinely uniform external-input interface over scale-indexed physical
configurations / hereditary source restrictions. Schematically:

```lean
def UniformGeomInput (d : ℕ) : Prop :=
  UniformSubpowerLE (AdmissibleGeomConfig d) pairEnergy rhs
```

The constructors/fields should distinguish the actual d=2, d=3, d=4 input
roles, but the common constant must be chosen before the concrete tube family,
tube count, marks, or subtree.

Deep results [2], [7,10], [9] may remain **named external hypotheses**. They
do not need to be re-proved here. Their *formal statement* must have the
correct uniform quantifiers.

### Acceptance test

The authoritative uniform theorem no longer gets a per-configuration field

```lean
geom_pair : ∀ x ∈ T, SubpowerLE ...
```

whose hidden constant may depend on that configuration.

---

## 3. Add a uniform descent-complexity certificate

The current local descent correctly extracts one constant for all proper
vertices of a **fixed finite tree** using `uniform_proper_const`. That is
not yet uniform across varying trees.

The current proper-predecessor estimate also explicitly contains the tree
height.

### Target

Formalize the paper's source-subpower complexity control, e.g. a certificate
that controls, uniformly over admissible configurations:

- refined history-tree height;
- relevant branching/alphabet complexity;
- finite support / confluence / Cartan ceilings when they enter constants;
- any finite maxima used by the induction.

Do not simply bound the full tree cardinality if the paper only needs height
or a smaller structural quantity; follow the paper's ledger.

A possible shape is:

```lean
structure UniformDescentComplexity ... where
  height : ...
  height_subpower : UniformSubpowerLE ... height 1
  ...
```

### Acceptance test

The constant produced by the uniform descent depends only on
`ε`, `d`, and explicitly approved fixed paper parameters, not on the
concrete `T`.

---

## 4. Uniformize the hardening ledger constants

`HardeningLedger` is now correctly shared across all subtrees of one tree,
but it remains local to one configuration.

Two quantities are especially important:

```lean
L.hcard : SubpowerLE (fun _ => card L.K) (fun _ => 1)
L.c₀
```

For a fixed finite `K`, the first statement is automatic if its constant may
depend on `K`. Likewise the final hardening constant contains a factor
proportional to `1 / c₀`.

### Target

At the uniform level, require/derive:

- carrier-count control with one constant before the configuration;
- a uniform or subpower control of `1 / c₀`;
- any other packet-class constants that survive
  `node_hardening_subpower`.

### Acceptance test

There is no route in the uniform proof that can choose
`Cκ = card K` separately for each configuration.

---

## 5. Remove hidden pre-`C` configuration complexity from the top theorem

Current theorem:

```lean
theorem scalar_closure_uniform
    {d : ℕ} {α : Type} [DecidableEq α] [Fintype α] : ...
```

fixes the finite label type `α` **before** `UniformSubpowerLE` chooses
`C`. Hence the final constant is formally allowed to depend on `α` and
its finite cardinality.

This is contrary to the stated goal that `C` not depend on the history
alphabet/configuration.

It also does not fit naturally with the source-derived faithful tree whose
node/state type depends on the scale-dependent tube count `n(δ)`.

### Target

Move configuration-specific label/state types inside the dependent
configuration, or otherwise prove explicitly that the constant is independent
of `α`.

For example, the final config may carry its own label type and instances:

```lean
structure UniformScalarConfig (d : ℕ) (δ : ℝ) where
  Label : Type
  instDecEqLabel : DecidableEq Label
  instFintypeLabel : Fintype Label
  ...
```

but then the uniform proof must control the resulting complexity through the
uniform descent certificate, not by depending on the type itself.

### Acceptance test

No arbitrary finite configuration-dependent type/value is quantified outside
the uniform `∃ C` unless it is an explicitly approved fixed parameter.

---

## 6. Fix the physical configuration's scale separation semantics

`PhysicalConfig d δ` is scale-indexed, but it currently contains a
`TubeFamily n d` whose field is

```lean
dir_separated :
  ∀ t ≠ t', ∀ δ', 0 < δ' → δ' < 1 →
    sep * δ' ≤ ‖dir t - dir t'‖
```

with `sep` itself stored in the concrete family.

This does **not** cleanly encode a universal `c · δ` direction separation
at the current scale with `c` independent of the configuration. A concrete
family can shrink its own `sep`.

### Target

Give the scale-indexed physical configuration a current-scale separation
condition with the comparison constant fixed outside the configuration, e.g.

```lean
cSep * δ ≤ ‖dir t - dir t'‖
```

for a fixed approved `cSep > 0`, or normalize to `δ ≤ ...`.

Prefer a genuinely single-scale physical object (`TubeFamilyAt δ`,
`ShadingAt δ`) if this removes irrelevant all-scale fields.

### Acceptance test

The class of admissible configurations in the uniform theorem is exactly the
intended direction-separated finite-scale Kakeya class, with no
configuration-dependent separation constant leakage.

---

# P1 — Finish the paper-faithful source provenance

## 7. Build loads from `pathMass`, not from representatives

The representative-leaf `SourceModel` was correctly removed.

The current faithful source facts are now:

- `packetSelectOfSource`;
- `derivedChildMass_sum`;
- `pathMass`;
- `pathMass_partition` (paper (133)).

The next step is to make the actual history loads come from the same physical
joint source/cylinder flow.

### Target

Construct the retained history load `u_γ` / integrated load from
`pathMass` (and the physical incidence source) so that the following are
theorems, not arbitrary model fields:

- nonnegativity;
- child-cylinder partition (133), preferably over the actual selected
  children rather than all possible states;
- root total-load identity (136) for the **retained source**;
- terminal-tube disintegration (143)/(145);
- the leaf bound used by the descent.

`termTube` must be derived from the terminal physical incidence/tube label,
not chosen as an unrelated function.

### Acceptance test

There is a source-derived constructor/theorem feeding the faithful tree whose
`load` and `termTube` come from the packet/incidence source, with no
representative-leaf device.

---

## 8. Treat deletion correctly: retained mass is not the original mass

This is now a crucial semantic point.

`derivedChildMass_sum` conserves

```text
retained ∩ survives-deletion
```

mass. It does **not** say that deletion preserves the full original shading
mass exactly.

Therefore the authoritative source path should not try to prove

```lean
totalLoad = ∑ originalShadeVol
```

after nonzero source-small deletion unless the paper genuinely gives that
identity.

Paper (130) keeps only a controlled fraction and paper (214) converts the
retained descendant back to an ordinary incidence statement.

### Target

Choose one paper-faithful formulation:

1. define a retained descendant shading `Sret` and prove the exact identity
   `totalLoad = ∑ Sret.shadeVol`, together with a uniform/subpower lower
   bound comparing retained mass to the original source; or
2. carry an explicit retained fraction `α` through the authoritative
   theorem and use the terminal threshold/unweighting step.

Connect the existing `SourceLedger` / Markov deletion facts to this bridge.

### Acceptance test

No proof of source conservation relies on pretending deleted mass is still
present. The final theorem explicitly recovers the original incidence scale
through the paper's retained-mass estimate.

---

## 9. Make hereditary geometry use the restricted subtree source

`geom_pair_of_geomInput` is algebraically proved given
`hcompat_sub` and `htotal_sub`.

However its current compatibility hypothesis identifies every proper
re-rooted subtree's terminal loads with the **full original**
`S.shadeVol`:

```lean
termLoad (reroot T x) ... t δ = S.shadeVol t δ
```

That is generally too strong for a proper subtree. The paper's hereditary
statement uses the source restricted to the corresponding cylinder/subtree.

### Target

Define the restricted physical/analytic object `S_x` (or equivalent
conditional source) attached to a node `x`, and prove:

```text
rerooted termLoad at x = shadeVol of S_x
rerooted totalLoad at x = total shading of S_x
```

Then apply the **uniform hereditary geometric input** to `S_x`.

### Acceptance test

The strongest path does not assume that every proper subtree reproduces the
full root shading.

---

## 10. Derive the hardening ledger from the same source

`HardeningLedger` is structurally improved, but the authoritative
fixed-config theorem still accepts:

```lean
L : HardeningLedger ...
hlinkAt
hquantAt
```

as named inputs.

### Target

Construct these from the same paper data that generate the history tree:

- `(θ,j,c)` class assignment;
- common-source packet aggregates;
- the R5 link (150)–(151);
- branch-density comparability;
- the coarse carrier family / count (152).

The per-node `clsAt` must be source-derived, not an arbitrary classifier.

### Acceptance test

The paper-faithful source constructor yields both the history tree and its
hardening ledger, and `NodeHLink` / `NodeHQuant` follow by theorem.

---

## 11. Finish transition provenance

`PacketSource.trans` currently carries

```lean
htrans_step : ∀ s U, DescentStep (trans s U) s
```

as a field.

That is a useful interface, but the final paper-faithful construction should
derive it from the actual first-failed-face / confluence / Cartan transition
rules.

### Acceptance test

Provide a concrete constructor for the paper's transition map whose
`htrans_step` proof follows from the defined support/confluence/Cartan
operation.

---

# P2 — Authoritative theorem and repository hygiene

## 12. Keep exactly one authoritative top-level claim

The intended authoritative endpoint is the uniform physical scalar theorem,
not the old fixed-`n` `SubpowerLE` statements.

Local theorems such as `scalar_closure_discharged` remain valuable internal
lemmas, but documentation must not present them as the final Kakeya-uniform
statement.

### Acceptance test

The authoritative dependency path is visibly:

```text
scale-indexed physical source
  -> paper packet/source ledger
  -> retained pathMass history loads
  -> faithful history tree + hardening ledger
  -> restricted subtree physical sources
  -> uniform d=2/3/4 geometric input
  -> uniform well-founded descent / root-cross gate
  -> retained ordinary incidence
  -> terminal unweighting to the original source
```

and no old trivial-tree/symmetric-toy route is in that dependency closure.

---

## 13. Eliminate the remaining `sorry` before claiming kernel-clean status

At the current audited HEAD the only real `sorry` is the proof of
`scalar_closure_uniform`.

Until it is removed, do not claim "zero sorry" or "0 warnings" for the full
default build.

If the uniform theorem is not yet provable because its assumptions are still
being redesigned, prefer temporarily exposing its type as a named
`Prop`/claim or clearly WIP theorem rather than presenting a `sorry` theorem
as completed.

### Acceptance test

Repository-wide scan:

- zero `sorry`;
- zero `sorryAx`;
- zero project custom `axiom` / `constant` / `opaque` / `extern`;
- authoritative theorem's `#print axioms` shows only the expected standard
  Lean/mathlib logical axioms.

---

## 14. Add regression guards for the new failure modes

In addition to `uniform_not_trivial`, add checks that catch:

- reintroduction of a configuration-local `C = n` route;
- configuration-local carrier-count constants;
- top-level dependence on a fixed finite label alphabet;
- loss of the current-scale direction-separation condition;
- an exact full-mass identity after a nonzero deletion step;
- a proper subtree being identified with the full root shading;
- authoritative imports falling back to the old simplified path;
- README/MAPPING claiming zero `sorry` while one exists.

Where practical, make these compile-time theorem tests rather than comments.

---

## 15. Synchronize README and MAPPING with the code

Current README is stale: it still reports zero `sorry`, while
`scalar_closure_uniform` contains one.

The documentation also predates several important developments:

- uniform API and scale-indexed config;
- ledger-based hardening integration;
- dimension-indexed `GeomInput`;
- packet-derived child mass and `pathMass_partition`;
- deliberate removal of the representative-leaf source model;
- removal of the symmetric toy scalar theorem.

### Acceptance test

README, MAPPING, and this TODO agree on:

- the authoritative theorem;
- the exact remaining named external inputs;
- the exact number of `sorry`s;
- which source/provenance bridges are proved versus still open.

---

# Recommended execution order from the current HEAD

1. **Repair the authoritative uniform specification**:
   remove hidden `α`/tree/carrier/separation dependence and define the
   uniform geom/hardening/complexity assumptions.
2. **Build the paper-faithful retained source model from `pathMass`**,
   including deletion/retention bookkeeping.
3. **Derive terminal-tube loads and root/retained mass identities** from that
   source.
4. **Define restricted subtree physical sources** and discharge hereditary
   geometric compatibility correctly.
5. **Derive `HardeningLedger`, `hlinkAt`, and `hquantAt` from the same
   source/carrier data**, with uniform (152) control.
6. **Prove a uniform version of the descent induction/root-cross closure**
   using the explicit uniform complexity budgets.
7. **Prove `scalar_closure_uniform` with no `sorry`**.
8. **Restore the paper's retained-to-original terminal unweighting step** in
   the authoritative physical theorem.
9. **Run axiom/source regression checks and synchronize README/MAPPING**.

---

# Current main blockers, in one sentence

The local faithful descent machinery is now largely in place; the remaining
work is to turn the paper's **single retained physical source** into all of the
tree/load/hardening/subtree data with **uniform constants across
scale-dependent configurations**, and only then close the one remaining
authoritative `scalar_closure_uniform` proof.
