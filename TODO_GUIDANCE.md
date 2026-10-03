# TODO Guidance — KakeyaDescent

Current audit target: main at commit
1ce5d824efa8640e2bd2e56c8a988fa0bbc03b2e (2026-10-03).

This document tracks the remaining work for a paper-faithful authoritative scalar theorem.

The repository is now source-level kernel-clean, but the newest scalar_closure_uniform closes by a uniform leaf-count shortcut rather than by the filtered-descent argument. The next work must therefore protect mathematical fidelity, not merely preserve Lean provability.

---

# 0. Current audited status

## Completed and worth keeping

- [x] UniformSubpowerLE has the correct outer quantifier order.
- [x] uniform_not_trivial blocks a simple configuration-dependent C = n(delta) proof.
- [x] PhysicalConfig is scale-indexed.
- [x] FaithfulModel is parameterized by the actual analytic family.
- [x] The faithful root split, duplicate identities, rerooting, and well-founded predecessor induction are proved.
- [x] node_hardening_subpower consumes subpower predecessor control.
- [x] HardeningLedger and per-node hardening data are threaded through the fixed-configuration descent.
- [x] scalar_closure_discharged derives terminal hardening from the ledger rather than taking a theorem-valued hardening hypothesis.
- [x] Dimension-indexed GeomInput and the algebraic hereditary conversion exist.
- [x] PacketSource derives child mass from the packet law.
- [x] derivedChildMass_sum proves one-step packet-mass fiber conservation.
- [x] pathMass / pathMass_partition formalize the child-cylinder partition behind paper (133).
- [x] The representative-leaf source model was removed.
- [x] The symmetric toy scalar theorem was removed.
- [x] The former final sorry in scalar_closure_uniform has been removed.

## Kernel/source hygiene

At the current HEAD:

- no actual sorry, admit, or sorryAx was found;
- no project custom axiom, constant, opaque, extern, or implemented_by was found in the audited formal core.

This is a real milestone.

However:

> 0 sorry does not currently mean the authoritative theorem follows the paper's descent.

The new top proof bypasses it.

---

# P0 — Remove the new top-level trivialization

## 1. Delete the fixed leaf-count shortcut from the authoritative theorem

Current admissibility adds a condition of the form

treeLeaves.card <= branching_bound ^ height_bound,

with both bounds fixed outside the varying configuration.

Then scalar_closure_uniform proves

sum shadeVol
= totalLoad
<= card(leaves) * unionVol
<= B^H * unionVol,

and finishes with 1 <= delta^(-epsilon).

This proof does not use:

- hU.geom;
- uniformGeomPair_to_local;
- HardeningLedger;
- hlinkAt;
- hquantAt;
- the faithful root-cross gate;
- the well-founded descent.

It therefore proves a bounded-leaf statement, not the filtered descent claimed by the paper.

### Target

Remove hadm_leaves as a hypothesis strong enough to imply the final scalar bound directly.

If the paper controls tree height or branching only by subpower factors, encode those factors as quantities consumed inside the descent, not as a fixed cardinality bound yielding the conclusion immediately.

### Acceptance test

The authoritative theorem must genuinely depend on

uniform geometric root-cross input
-> hardening / predecessor induction
-> faithful gate
-> scalar closure.

Deleting the root-cross/descent imports must make the authoritative theorem fail to compile.

---

## 2. Replace UniformDescentComplexity by paper-faithful subpower complexity

Current UniformDescentComplexity stores fixed natural-number bounds for tree height and branching.

That is substantially stronger than the paper's refined-history control H_{I,k} = delta^{-o(1)} and related subpower structural losses.

### Target

Track exactly the complexity quantities that enter the paper estimates:

- history height;
- support/confluence/Cartan bookkeeping;
- carrier counts;
- finite maxima created by the Lean induction.

They should be controlled by uniform subpower estimates, not by a fixed global bound on all leaves.

### Acceptance test

Admissible configurations may have a number of histories/leaves growing with delta^{-1}, provided the paper's approved structural losses remain delta^{-o(1)}.

---

# P0 — Fix UniformGeomInput: current statement is too strong

## 3. Do not quantify over arbitrary nonnegative tubeLoad

Current AdmissibleGeomConfig contains an arbitrary nonnegative tubeLoad with no source/shading compatibility.

Then UniformGeomInput requires the pair estimate for every such load.

This is generally impossible. If two tube loads are scaled by lambda, then

pairEnergy grows like lambda^2,
while geomRHS grows like lambda.

So no fixed uniform constant can control arbitrary lambda.

Thus UniformGeomInput in its current form is likely uninhabited for any nontrivial family with at least two tubes.

### Target

The geometric input must quantify only over loads arising from the relevant paper class:

- actual shaded tube families;
- retained/source-restricted descendants;
- hereditary subtree sources;
- marked variants in d=4.

Do not allow a free arbitrary tubeLoad.

### Acceptance test

Construct at least one nontrivial admissible d=2/d=3/d=4 geometric configuration from the intended physical source.

Add a regression preventing arbitrary rescaling of tubeLoad unless the physical/shading source is rescaled in the corresponding legal way.

---

## 4. Derive subtree geometric loads from restricted physical sources

The current admGeomConfigOfSubtree inserts rerooted termLoad into the overly broad geometric configuration.

That makes threading syntactically easy, but does not prove that the load belongs to the class on which Cordoba/sticky/marked-4D applies.

### Target

For every retained node x, construct the actual restricted source/shading S_x and prove:

- rerooted terminal tube load = shading load of S_x;
- rerooted total load = total shading mass of S_x.

Then instantiate the uniform geometric theorem on S_x.

### Acceptance test

uniformGeomPair_to_local cannot be instantiated from an arbitrary nonnegative function; it requires a source-derived subtree geometry witness.

---

# P0 — Force the authoritative theorem back through the descent

## 5. scalar_closure_uniform must call the real descent machinery

The current proof never invokes the machinery that the theorem is supposed to formalize.

### Target

Build a uniform version of the fixed-configuration chain:

source/tree data
-> uniform local geom_pair
-> node_hardening_subpower
-> descent_bound / faithful_gate_discharged
-> N^2 <= subpower * Bpred * N
-> scalar division.

All constants must be tracked uniformly from UniformDescentAssumptions.

### Acceptance test

The final proof visibly consumes hU.geom and the hardening/complexity certificates. No component of UniformDescentAssumptions may be decorative.

---

## 6. Make the uniform hardening budget actually constrain the local ledger

UniformHardeningBudget stores global quantities, but the current top proof does not use them, while each local HardeningLedger still carries its own hcard and c0.

### Target

Add explicit compatibility between every local ledger and the uniform budget:

- carrier count controlled uniformly;
- inverse c0 controlled uniformly or subpower-uniformly;
- any other constants surviving node_hardening_subpower controlled uniformly.

### Acceptance test

A local ledger with arbitrarily huge carrier alphabet or arbitrarily tiny c0 cannot enter an admissible uniform configuration without paying the approved subpower loss.

---

## 7. Remove hidden dependence on the fixed label type alpha

The theorem still fixes a finite label type alpha before UniformSubpowerLE chooses its constant.

Therefore the final constant is formally allowed to depend on alpha, although the theorem documentation says it should not depend on the history alphabet.

### Target

Either move the configuration-specific label/state type inside the dependent configuration, or prove an explicit uniformity theorem whose constant is independent of alpha.

### Acceptance test

No arbitrary finite configuration-dependent type is fixed before the top existential constant unless it is an explicitly approved fixed paper parameter.

---

## 8. Fix current-scale direction separation

PhysicalConfig is scale-indexed, but TubeFamily still carries its own configuration-dependent positive sep and an all-scale condition.

### Target

Encode the intended finite-scale direction separation with a comparison constant fixed outside the varying configuration, for example cSep * delta <= distance of directions, or normalized delta-separation.

### Acceptance test

An admissible sequence cannot weaken the geometric hypothesis by sending its private separation constant to zero.

---

# P1 — Finish the paper-faithful retained source

## 9. Build history loads from pathMass

The representative-leaf workaround was correctly deleted.

The current source primitives are the right direction:

- packetSelectOfSource;
- derivedChildMass_sum;
- pathMass;
- pathMass_partition.

### Target

Construct the actual retained history load from the same packet/incidence source so that the following become theorems:

- nonnegativity;
- child partition (133);
- root identity (136) for the retained source;
- terminal tube decomposition (143)/(145);
- the leaf bound used by the descent.

termTube must come from the terminal physical incidence label rather than be an unrelated function parameter.

### Acceptance test

A single paper-faithful source constructor provides the tree, load, terminal tube labels, and their mass identities.

---

## 10. Do not equate retained mass with original mass after deletion

derivedChildMass_sum conserves retained/surviving packet mass. It does not restore deleted mass.

### Target

Follow paper (130) and (214):

- define the retained descendant physical shading/source;
- prove exact mass identities for that retained object;
- prove the retained fraction / source-small loss;
- perform terminal weighted-to-unweighted recovery to the original incidence source.

### Acceptance test

No post-deletion theorem claims retained totalLoad = original total shading unless deletion is actually zero.

---

## 11. Derive the hardening ledger from the same source

The fixed-configuration main chain still takes HardeningLedger, hlinkAt, and hquantAt as source-independent inputs.

### Target

Construct from the same packet/history source:

- the (theta,j,c) classifier;
- common-source aggregates;
- R5 link (150)-(151);
- density comparability;
- carrier family/count (152).

### Acceptance test

The source constructor yields both the history tree and the hardening ledger; NodeHLink and NodeHQuant are proved, not independently assumed.

---

## 12. Derive the transition map from the actual descent operations

PacketSource.trans still carries htrans_step as a field.

### Target

Define the transition from the actual first-failed-face / support / confluence / Cartan operation and prove the label decrease.

### Acceptance test

The strongest source path does not inject an arbitrary state transition with the desired decrease property already attached.

---

# P2 — Repository and theorem hygiene

## 13. Redesign AdmissibleUniformScalarConfig

The current name suggests paper-admissible, but its decisive condition is the non-paper fixed leaf-count shortcut.

### Target

Replace it with a configuration whose fields express exactly the paper hypotheses and the uniform certificates needed by the real descent.

No field may directly imply the final scalar estimate by elementary finite summation.

### Acceptance test

Try to prove the final bound after removing all root-cross/descent lemmas. The proof should fail.

---

## 14. Add non-vacuity regression tests

Add checks for both forms of accidental vacuity discovered so far:

1. too-strong conclusion-bearing admissibility;
2. uninhabitable external input.

Useful regressions:

- exhibit a nontrivial admissible geometric configuration;
- exhibit a nontrivial admissible uniform scalar configuration built from the intended source data;
- prove admissibility is preserved under the actual hereditary restriction used by the paper.

---

## 15. Keep the authoritative dependency closure auditable

The final dependency path should be:

scale-indexed physical source
-> packet/source ledger
-> retained pathMass history loads
-> faithful history tree + hardening ledger
-> restricted subtree physical source
-> uniform d=2/3/4 geometric input
-> uniform well-founded descent
-> faithful root-cross gate
-> retained scalar incidence
-> terminal unweighting to original source.

No direct bounded-cardinality argument should bypass this path.

---

## 16. Synchronize README / MAPPING / TODO

The README's zero-sorry claim is now consistent with the audited source, but much of its remaining-hypotheses section predates the latest ledger and uniform refactors.

### Acceptance test

README, MAPPING, and this TODO agree on:

- which theorem is authoritative;
- whether that theorem actually follows the filtered-descent path;
- the exact named external geometric hypotheses;
- which source bridges are proved versus open;
- the current axiom/sorry status.

---

# Recommended execution order from current HEAD

1. Remove the fixed leaf-count shortcut from the authoritative theorem.
2. Restrict UniformGeomInput to actual source-derived geometric loads.
3. Define paper-faithful uniform complexity controls.
4. Wire the uniform hardening budget to every local ledger.
5. Make scalar_closure_uniform consume the real descent/gate.
6. Build retained history loads and terminal labels from pathMass.
7. Construct hereditary restricted physical sources S_x.
8. Derive hardening ledgers from the same source.
9. Carry deletion/retained fraction through terminal unweighting.
10. Remove hidden alpha/separation-constant dependence.
11. Add non-vacuity and dependency regression tests.
12. Synchronize README/MAPPING after the corrected authoritative theorem is in place.

---

# Current main blocker, in one sentence

The repository is now 0-sorry, but the authoritative uniform theorem is currently true for the wrong reason: a fixed leaf-count assumption makes the scalar estimate elementary, while the stated uniform geometric input is too broad to be obviously inhabitable; the next revision must restore the actual paper-faithful source -> subtree geometry/hardening -> descent -> root-cross dependency chain.
