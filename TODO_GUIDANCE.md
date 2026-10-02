# TODO Guidance — KakeyaDescent

This file records the highest-priority formalization work needed before the repository can be regarded as a faithful machine-checked implementation of the paper's scalar filtered descent.

The guiding principle is:

> Prefer fixing theorem **specifications and quantifier order** before adding more downstream lemmas. A kernel-clean proof of a statement whose constants may depend on the finite tube count is not yet the Kakeya-uniform statement used in the paper.

## P0 — Fix asymptotic uniformity first

### 1. Replace the current family-local `SubpowerLE` by a configuration-uniform notion

Current shape:

```lean
def SubpowerLE (x y : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ C ≥ 0, ∀ δ, 0 < δ → δ < 1 →
    x δ ≤ C * δ ^ (-ε) * y δ
```

When a theorem first fixes `n`, `S : ShadedTubes n`, a tree, or a finite carrier type `K`, the witness `C` may depend on all of them. This makes several intended asymptotic statements formally too weak.

In particular, for fixed `n`:

```text
∑ₜ shadeVol t δ ≤ n * unionVol δ
```

already implies the current scalar closure by taking `C = n`.

Likewise, for a fixed finite type `K`:

```text
card K ≲ 1
```

is automatic by taking `C = card K`, so this does not yet encode paper (152).

**Target:** introduce a uniform notion whose constant is quantified before the family/configuration.

Suggested design sketch:

```lean
def UniformSubpowerLE
    (Config : ℝ → Type)
    (X Y : ∀ δ, Config δ → ℝ) : Prop :=
  ∀ ε > 0,
    ∃ C ≥ 0,
      ∀ δ, 0 < δ → δ < 1 →
      ∀ cfg : Config δ,
        X δ cfg ≤ C * δ ^ (-ε) * Y δ cfg
```

The exact API can differ, but the key requirement is:

- `C` may depend on `ε` and the ambient dimension / fixed paper parameters;
- `C` must **not** depend on the tube count, the concrete tube family, the history tree, the retained packet subset, or the carrier alphabet;
- the configuration type may depend on `δ`.

### Acceptance test

Add a regression theorem showing that the API does **not** allow the trivial proof by `C = n` when `n = n(δ)` is allowed to grow.

A good test configuration is one with `n(δ) ≍ δ^{-(d-1)}`.

---

### 2. Make tube families scale-indexed

The physical model currently fixes `TubeFamily n d` and lets only `δ` vary.

For Kakeya finite-scale asymptotics, the relevant family generally changes with `δ`, and its cardinality may grow like a power of `δ^{-1}`.

**Target:** formalize a scale-indexed physical configuration, for example:

```lean
structure PhysicalConfig (d : ℕ) (δ : ℝ) where
  n : ℕ
  family : TubeFamily n d
  shading : Shading family
  ...
```

or an equivalent dependent formulation.

The final scalar theorem should quantify over the physical configuration *after* choosing the uniform constant.

### Acceptance test

The final top-level scalar statement should remain meaningful when the number of tubes varies with `δ`.

---

## P0 — Fix the current `FaithfulModel` specification

### 3. Parameterize `FaithfulModel` by the actual analytic family

Current `FaithfulModel` has a fixed `loadOf` but requires:

```lean
mass_conserved :
  ∀ (s : DescentState α n) (S : ShadedTubes n) (δ : ℝ),
    ...
    = ∑ t, S.shadeVol t δ
```

For `n > 0`, this asks one fixed load to equal the total shading mass of **every** possible `S`, so the structure is generally uninhabited.

**Target:** parameterize the structure by the actual `S` (and, if useful, by the root state):

```lean
structure FaithfulModel ... (S : ShadedTubes n) where
  ...
  mass_conserved :
    ∀ s δ, ...
  leaf_geometric :
    ∀ γ δ, ...
```

Do not quantify over arbitrary unrelated `S` inside the structure.

### Acceptance test

Construct at least one nontrivial `FaithfulModel` instance for a concrete `S` with `n > 0`.

---

## P1 — Integrate F7 into the actual induction

### 4. Upgrade F7 hardening from pointwise `Hpred` to subpower `Hpred`

Current F7 theorem:

```lean
node_hardening_via_streamB
```

requires a pointwise predecessor bound

```lean
nodeAgg ... a ≤ Bpred δ
```

but the well-founded induction now proves only

```lean
SubpowerLE (fun δ => nodeAgg ... a) Bpred
```

This mismatch prevents F7 from discharging the `terminal_hardening` hypothesis in the end-to-end chain.

**Target:** re-run the (149)–(153) argument with a uniform subpower predecessor constant.

The intended route is:

1. use the finite set of proper predecessor nodes to extract one common
   `C_ε δ^{-ε}` bound (the existing `uniform_proper_const` idea);
2. thread that loss through the active-child estimate / `hlink`;
3. absorb it into the global subpower ledger;
4. keep `hquant` and the lower-density comparison correctly oriented;
5. avoid replacing `Bpred` by a larger ad hoc bound in a way that destroys the lower-bound side of `hquant`.

This proof likely belongs *inside* the well-founded descent step, not as a post-processing lemma, because a post-hoc argument risks circularity.

### Acceptance test

`scalar_closure_discharged` should no longer take

```lean
terminal_hardening : ∀ x ∈ T, ...
```

as a theorem parameter.

Instead, terminal hardening should be constructed from per-node `HardeningInputs` plus the induction hypothesis.

---

### 5. Thread `HardeningInputs` per re-rooted subtree

F7 currently gives the correct local theorem once the `HardeningInputs` for that subtree are supplied.

**Target:** define the per-node/per-subtree data source:

```lean
hardeningInputsAt :
  ∀ x ∈ T, HardeningInputs ((treeChildren (reroot T x) []).card) n
```

together with the corresponding `hlink` and `hquant`.

These should come from the same packet/source ledger that constructs the faithful tree, not from unrelated arbitrary functions.

### Acceptance test

The re-rooted hardening theorem should be instantiated for every internal node without introducing a new unrelated model at each node.

---

## P1 — Make the geometric input genuinely hereditary

### 6. Replace family-level pair-bound aliases by paper-faithful geometric interfaces

Currently `PlanarInput`, `StickyInput`, and `Marked4DInput` all have essentially the same abstract pair-incidence shape.

That is acceptable as an intermediate consumer interface, but it should not be presented as a formalization of paper (53), (177), and (81) themselves.

**Target:** distinguish:

- the external paper theorem interface;
- the conversion from that theorem to the exact `geom_pair` needed by a re-rooted subtree.

For example:

```text
PlanarCordobaInput
  -> planar subtree conversion
  -> geom_pair at d = 2

StickyKakeyaInput
  -> sticky/non-sticky factorization + hereditary subtree conversion
  -> geom_pair at d = 3

Marked4DInput
  -> marked-fibre hereditary conversion
  -> geom_pair at d = 4
```

### Acceptance test

`geom_pair : ∀ x ∈ T, ...` should be produced by a theorem from the relevant dimension-specific input and the source-compatible subtree data, rather than passed directly to `scalar_closure_discharged`.

---

## P1 — Finish the tree/source provenance

### 7. Derive `PacketSelect.childMass` from the packet law

Current `PacketSelect` stores `childMass` as arbitrary data and then defines realized children by positivity.

**Target:** prove that the selected child masses arise from:

- the common packet probability law;
- first-failed-face assignment;
- retained-mass restriction;
- insertion/confluence kernels;
- the source-small deletion ledger.

The tree should be a deterministic/derived object of the source ledger, not an arbitrary positive-mass child selector.

### Acceptance test

Replace or wrap `PacketSelect` with a constructor theorem from the packet/source data, and use that constructor in the faithful top-level path.

---

### 8. Discharge `htotalLoad` from the same source construction

The final theorem should not separately assume

```lean
htotalLoad : totalLoad T load δ = ∑ t, shadeVol t δ
```

if the tree/load system is supposed to be constructed from the packet law.

**Target:** derive this identity from source mass conservation and the leaf partition.

### Acceptance test

Remove `htotalLoad` from the strongest top-level theorem's parameter list.

---

## P2 — Top-level theorem hygiene

### 9. Define one authoritative top theorem

There are currently several overlapping scalar theorems:

- old simplified path;
- faithful pointwise-`Hpred` path;
- discharged-`Hpred` path;
- physical wrappers;
- constructed symmetric model-validation path.

Keep old theorems if useful, but designate exactly one authoritative theorem whose type matches the intended mathematical claim.

The authoritative theorem should:

- use the scale-indexed physical configuration;
- use the uniform asymptotic relation;
- have no trivial `C = n` proof;
- not assume `Hpred`;
- not assume `terminal_hardening`;
- not assume `geom_pair` directly, only the named external d=2/3/4 input;
- derive the physical tree/load bridges from the construction.

### Acceptance test

A dependency audit of the authoritative theorem should visibly pass through:

```text
physical source
  -> packet/source ledger
  -> faithful history tree
  -> per-subtree hardening
  -> per-subtree geometric input
  -> well-founded descent
  -> faithful root-cross gate
  -> scalar incidence
```

---

### 10. Add compile-time / source-level regression guards

Add lightweight checks that fail if the specification regresses.

Suggested checks:

- a theorem or test showing the authoritative uniform statement cannot be discharged by `C = n`;
- `#print axioms` for the authoritative theorem;
- grep/source scan for `sorry`, `sorryAx`, custom `axiom`, `constant`, `opaque`, `extern`;
- a check that the authoritative theorem imports the faithful path, not the old trivial-tree path;
- a check that no theorem named “physical” merely wraps an abstract `ShadedTubes n` statement with family-local constants;
- a check that the README status matches the strongest theorem actually proved.

---

## P2 — Documentation / claims

### 11. Keep README and MAPPING conservative

Until the P0/P1 items above are closed, keep the repository labeled:

> Work in progress; kernel-clean formalization of the faithful descent machinery with explicit remaining analytic/construction inputs.

Do not call the repository a complete formalization of the paper until:

1. asymptotic constants are uniform over scale-dependent configurations;
2. the faithful model is inhabited from actual source data;
3. per-subtree hardening is derived, not assumed;
4. per-subtree geometric input is derived from the stated d=2/3/4 theorem interfaces;
5. the authoritative top theorem has the intended physical quantifier order.

---

## Recommended execution order

1. **Uniform asymptotic API** — highest priority.
2. **Fix `FaithfulModel` parameterization.**
3. **Refactor theorem signatures to the uniform API.**
4. **F7-subpower fusion inside the well-founded induction.**
5. **Per-subtree `HardeningInputs` threading.**
6. **Per-subtree dimension-specific `geom_pair` conversion.**
7. **Packet law → selected tree/load provenance.**
8. **Discharge `htotalLoad`.**
9. **Define the single authoritative physical theorem.**
10. **Only then upgrade README status.**

---

## Current assessment at commit 260869f84ed44c2e718c304d44488df548517717

What is already genuinely valuable:

- no project-specific axioms / no `sorry` in the formal core;
- general history-tree combinatorics;
- exact faithful root split and duplicate identities;
- re-rooting infrastructure;
- well-founded `Hpred` induction;
- real Euclidean tube/shading realization;
- stream-B terminal-hardening theorem;
- F7 node-hardening bridge from pointwise predecessor control.

Main blockers:

1. asymptotic uniformity is still family-local;
2. `FaithfulModel.mass_conserved` is over-quantified in `S`;
3. F7 still needs pointwise `Hpred`, while the induction gives subpower `Hpred`;
4. per-subtree hardening/geometry/source provenance are not yet fully constructed.

This ordering should be preserved: **fix the theorem specification before spending effort on additional downstream lemmas.**
