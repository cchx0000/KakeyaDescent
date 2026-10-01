#!/usr/bin/env python3
"""Add 18 draft items (6 defs + 12 theorems) to the mission proposal."""
import json, urllib.request, urllib.error, os, sys, time

TOKEN = open('/tmp/p2m_token').read().strip()
PROP_ID = open('/tmp/proposal_id').read().strip()
BASE = "https://prove2.me/api/v1"
LEAN = "/home/hatch/workspace/prove2me-paper/lean"
PAPER_URL = "https://cchx0000.github.io/papers/filtered-descent-physical-kakeya/filtered-descent-physical-kakeya.pdf"

def read_lean(path):
    with open(os.path.join(LEAN, path)) as f:
        return f.read()

def api_post(path, data, retries=3):
    url = BASE + path
    body = json.dumps(data).encode()
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, data=body, headers={
                "Authorization": f"Bearer {TOKEN}",
                "Content-Type": "application/json",
            }, method="POST")
            with urllib.request.urlopen(req, timeout=60) as resp:
                return resp.status, json.load(resp)
        except urllib.error.HTTPError as e:
            print(f"  HTTP {e.code}: {e.read().decode()[:800]}")
            return e.code, None
        except Exception as e:
            print(f"  Attempt {attempt+1} failed: {e}")
            time.sleep(2)
    return None, None

items = []

# --- 6 Definitions ---
items.append({
    "kind": "definition",
    "definition_name": "FilteredDescent.SubpowerLE",
    "definition_title": "Subpower bound $\\lesssim_\\delta$",
    "definition": read_lean("Definitions/Def_FilteredDescent_Subpower.lean"),
    "natural_language_statement": "A quantity $x$ is subpower-bounded by $y$ at scale $\\delta$, written $x \\lesssim_\\delta y$, if for every $\\varepsilon > 0$ there exists $C \\geq 0$ (independent of $\\delta$) with $x \\leq C\\, \\delta^{-\\varepsilon}\\, y$. Includes the reflexivity and right-transitivity lemmas.",
    "source": f"Cai, Filtered Descent for the Physical Kakeya Incidence, 2026, {PAPER_URL}, §1 (the $\\delta^{{-o(1)}}$ convention)",
    "tags": ["harmonic-analysis", "kakeya", "asymptotics"],
})

items.append({
    "kind": "definition",
    "definition_name": "FilteredDescent.Packet",
    "definition_title": "Ordered packet law, slot marginal, retained mass",
    "definition": read_lean("Definitions/Def_FilteredDescent_Packet.lean"),
    "natural_language_statement": "An ordered $r$-packet $U$ over $n$ tubes with weights $w$ has law $\\prod_j w(U_j)/W^r$ where $W = \\sum_i w_i$. The slot-$s$ marginal $\\mu_s(x)$ and the retained mass $\\alpha = \\sum_{U \\in A} \\prod_j w(U_j)/W^r$ of a packet event $A$ are defined from it.",
    "source": f"Cai, Filtered Descent for the Physical Kakeya Incidence, 2026, {PAPER_URL}, §2 (R5 setup, (9), (25))",
    "tags": ["harmonic-analysis", "kakeya", "probability"],
})

items.append({
    "kind": "definition",
    "definition_name": "FilteredDescent.Kernel",
    "definition_title": "Slot marginal law and insertion kernels",
    "definition": read_lean("Definitions/Def_FilteredDescent_Kernel.lean"),
    "natural_language_statement": "For a law $P$ on packets supported on slot set $A$, the slot-$s$ marginal law $\\mu_{P,A,s}$ is the pushforward. The insertion kernel $\\kappa^A_{s,x}(P)$ inserts $x$ at slot $s$ when the existing entries agree with $A$ and the marginal is positive, and is the zero kernel otherwise.",
    "source": f"Cai, Filtered Descent for the Physical Kakeya Incidence, 2026, {PAPER_URL}, §3 ((13)–(16))",
    "tags": ["harmonic-analysis", "kakeya", "probability"],
})

items.append({
    "kind": "definition",
    "definition_name": "FilteredDescent.Tree",
    "definition_title": "History tree: leaves, node aggregates, LCA, root-cross mass",
    "definition": read_lean("Definitions/Def_FilteredDescent_Tree.lean"),
    "natural_language_statement": "A history tree is a prefix-closed finite set of words. Leaves carry a load $u$. Node aggregate $W_a = \\sum_{\\gamma \\supset a} u_\\gamma$. The least common ancestor $a(\\gamma,\\gamma')$ is the longest common prefix. $X^{\\mathrm{root}}$ sums $u_\\gamma u_{\\gamma'}$ over leaf pairs with $a(\\gamma,\\gamma') = []$; $X^{\\mathrm{dup}}$ restricts to pairs sharing a terminal tube; $X^{\\mathrm{geom}}$ to pairs with distinct terminal tubes.",
    "source": f"Cai, Filtered Descent for the Physical Kakeya Incidence, 2026, {PAPER_URL}, §9–10 ((131)–(141), (143)–(155))",
    "tags": ["harmonic-analysis", "kakeya", "combinatorics"],
})

items.append({
    "kind": "definition",
    "definition_name": "FilteredDescent.Pivot",
    "definition_title": "Gram–Schmidt pivot quantities",
    "definition": read_lean("Definitions/Def_FilteredDescent_Pivot.lean"),
    "natural_language_statement": "For vectors $v_1,\\dots,v_r$ in $\\mathbb{R}^d$, $G_k$ is the $k \\times k$ Gram matrix of the first $k$ vectors, and the pivot $\\pi_k^2 = \\det G_{k+1}/\\det G_k$ is the squared orthogonal distance of $v_{k+1}$ from the span of the previous vectors.",
    "source": f"Cai, Filtered Descent for the Physical Kakeya Incidence, 2026, {PAPER_URL}, §4 ((32)–(42))",
    "tags": ["harmonic-analysis", "kakeya", "linear-algebra"],
})

items.append({
    "kind": "definition",
    "definition_name": "FilteredDescent.Analytic",
    "definition_title": "Analytic inputs: planar, sticky, marked-4D, shaded tubes, gate stage",
    "definition": read_lean("Definitions/Def_FilteredDescent_Analytic.lean"),
    "natural_language_statement": "The three imported analytic estimates as predicates: the hereditary planar Córdoba input, the sticky Kakeya input, and the uniform marked 4D sticky input — each asserting a subpower incidence bound. Plus the `ShadedTubes` record (shading volumes, union volume, multiplicity) and the `GateStage` record bundling a history tree with the tube family it is built over.",
    "source": f"Cai, Filtered Descent for the Physical Kakeya Incidence, 2026, {PAPER_URL}, §5–8, §11 ((53), (81), (177), (142))",
    "tags": ["harmonic-analysis", "kakeya"],
})

# --- 12 Theorems ---
def thm(name, title, file, nl, source_ref, tags, milestone):
    code = read_lean(f"Theorems/{file}")
    # Extract preamble (imports) and formal_statement (namespace block)
    lines = code.split("\n")
    preamble_lines = [l for l in lines if l.startswith("import ")]
    # formal_statement = everything from "namespace" onwards
    ns_start = next(i for i, l in enumerate(lines) if l.startswith("namespace "))
    formal = "\n".join(lines[ns_start:])
    return {
        "kind": "theorem",
        "theorem_name": name,
        "theorem_title": title,
        "formal_statement": formal,
        "natural_language_statement": nl,
        "preamble": "\n".join(preamble_lines),
        "source": f"Cai, Filtered Descent for the Physical Kakeya Incidence, 2026, {PAPER_URL}, {source_ref}",
        "tags": tags,
    }

items.append(thm(
    "FilteredDescent.r5_marginal_bound",
    "R5 marginal bound",
    "Thm_FilteredDescent_R5.lean",
    "Conditioning an ordered packet law on an event $A$ of retained mass $\\alpha > 0$ preserves each slot's marginal up to the factor $\\alpha^{-1}$: the conditioned slot marginal equals the unconditioned one, and is pointwise $\\leq \\alpha^{-1}$ times the base tube law.",
    "§2 (R5; (9), (25))",
    ["harmonic-analysis", "kakeya", "probability"], "M1"))

items.append(thm(
    "FilteredDescent.ordered_cauchy_binet",
    "Ordered Cauchy–Binet packet identity",
    "Thm_FilteredDescent_OrderedCauchyBinet.lean",
    "For $0 < d \\leq n$ and nonnegative weights $w$, summing $(\\prod_b w_{U_b}) \\cdot \\det(S_U)^2$ over all ordered $d$-tuples $U : [d] \\to [n]$ equals $d! \\cdot \\det(\\sum_i w_i s_i s_i^T)$, the weighted Gram determinant.",
    "§2 ((6))",
    ["harmonic-analysis", "kakeya", "linear-algebra"], "M2"))

items.append(thm(
    "FilteredDescent.kernel_chain_confluence",
    "Insertion kernel chain rule and confluence",
    "Thm_FilteredDescent_KernelChain.lean",
    "Insertion kernels satisfy the chain rule $\\kappa^B_{s,x} \\circ \\kappa^A = \\kappa^A_{s,x}$ for $A \\subseteq B \\subseteq C$, and two-slot insertion is confluent: inserting $i$ then $j$ equals inserting $j$ then $i$ (both equal the direct two-slot kernel).",
    "§3 ((13)–(16))",
    ["harmonic-analysis", "kakeya", "probability"], "M3"))

items.append(thm(
    "FilteredDescent.pivot_dichotomy",
    "Gram–Schmidt pivot dichotomy",
    "Thm_FilteredDescent_PivotDichotomy.lean",
    "For $r$ vectors with positive-definite Gram matrices: (1) $\\prod_k \\pi_k^2 = \\det(S)^2$; (2) either some pivot is broad ($\\pi_k^2 > \\kappa^2$) or all are narrow; (3) in the broad case $\\det(S)^2 \\geq \\kappa^{2r}$.",
    "§4 ((32)–(42))",
    ["harmonic-analysis", "kakeya", "linear-algebra"], "M4"))

items.append(thm(
    "FilteredDescent.tree_lca_reduction",
    "History-tree LCA reduction",
    "Thm_FilteredDescent_TreeLCA.lean",
    "Splitting the leaf-pair sum $\\sum_{\\gamma,\\gamma'} u_\\gamma u_{\\gamma'}$ by least common ancestor: pairs whose LCA is a proper node are controlled by the induction bound $W_a \\leq B$ at each of $\\leq D$ tree levels, giving $\\sum u_\\gamma u_{\\gamma'} \\leq D \\cdot B \\cdot \\sum u_\\gamma + X^{\\mathrm{root}}$.",
    "§9 ((131)–(141))",
    ["harmonic-analysis", "kakeya", "combinatorics"], "M5"))

items.append(thm(
    "FilteredDescent.duplicate_closure",
    "Common-source duplicate closure",
    "Thm_FilteredDescent_DuplicateClosure.lean",
    "$X^{\\mathrm{root}} = X^{\\mathrm{geom}} + X^{\\mathrm{dup}}$ exactly, and the duplicate part — root-cross pairs sharing a terminal tube — is bounded by $(\\#\\text{carriers}) \\cdot (A \\cdot B) \\cdot \\sum u_\\gamma$ via the per-carrier aggregate bound.",
    "§10 ((143)–(155))",
    ["harmonic-analysis", "kakeya", "combinatorics"], "M6"))

items.append(thm(
    "FilteredDescent.r5_insufficiency_model",
    "R5 insufficiency model",
    "Thm_FilteredDescent_R5Insufficiency.lean",
    "The paper's one-point model: $R \\geq 2$ unit-mass histories in a single tube satisfy chartwise R5 with $B = 1$ ($\\int N = R$) but $X^{\\mathrm{root}} = R^2 - R$, so no $R$-independent bound $X^{\\mathrm{root}} \\leq C \\cdot B \\cdot \\int N$ holds — chartwise R5 does not imply the duplicate bound.",
    "§10.5",
    ["harmonic-analysis", "kakeya"], "M6"))

items.append(thm(
    "FilteredDescent.root_cross_gate",
    "Root-cross gate (d = 2, 3, 4)",
    "Thm_FilteredDescent_RootCrossGate.lean",
    "Assuming the three imported analytic estimates (hereditary planar Córdoba [2], sticky Kakeya [7,10], uniform marked 4D sticky [9]) and the duplicate closure, the root-cross mass satisfies $X^{\\mathrm{root}} \\lesssim_\\delta B^{\\mathrm{pred}} \\cdot \\int N$ for $d \\in \\{2,3,4\\}$. Dimensions $d \\geq 5$ are not claimed.",
    "§11 ((142))",
    ["harmonic-analysis", "kakeya"], "M7"))

items.append(thm(
    "FilteredDescent.support_recurrence_closure",
    "Closed support recurrence",
    "Thm_FilteredDescent_SupportRecurrence.lean",
    "From the base case $|I| \\leq 2$ and the support-step recurrence (each $B_I$ with $|I| > 2$ is subpower-dominated by some strictly smaller support's cutoff), strong induction on $|I|$ gives $B_I \\lesssim_\\delta 1$ for all $I$.",
    "§12 ((124)–(125))",
    ["harmonic-analysis", "kakeya"], "M8"))

items.append(thm(
    "FilteredDescent.terminal_incidence_count",
    "Terminal incidence count",
    "Thm_FilteredDescent_TerminalCount.lean",
    "The terminal unweighting: with retained mass $\\alpha$ and multiplicity $M$ both subpower in $\\delta$, $\\bigcup_T Y(T) \\geq \\frac{\\alpha}{2M} \\sum_T |Y(T)|$ implies the incidence count $\\sum_T |Y(T)| \\lesssim_\\delta |\\bigcup_T Y(T)|$.",
    "§13 ((130) → (214))",
    ["harmonic-analysis", "kakeya"], "M8"))

items.append(thm(
    "FilteredDescent.unweighted_projection_false",
    "Unweighted projection is false",
    "Thm_FilteredDescent_UnweightedProjectionFalse.lean",
    "Counterexample: two unit-weight tubes, one packet slot, singleton event $\\{U = (0,)\\}$. The conditioned slot marginal is $1$ but the unconditioned marginal is $1/2$ — conditioning does not preserve marginals, and R5's $\\alpha^{-1}$ factor is exactly the repair.",
    "§2 ((54))",
    ["harmonic-analysis", "kakeya", "probability"], "M9"))

items.append(thm(
    "FilteredDescent.scalar_closure",
    "Scalar filtered-descent closure (goal)",
    "Thm_FilteredDescent_ScalarClosure.lean",
    "The paper's scalar closure: for a finite direction-separated family of shaded $\\delta$-tubes with $\\lambda_{\\mathrm{in}}^{-1} = \\delta^{-o(1)}$, assuming the three imported analytic estimates, the terminal incidence count $\\sum_T |Y(T)| \\lesssim_\\delta |\\bigcup_T Y(T)|$ holds for $d \\in \\{2,3,4\\}$.",
    "§13.2 ((214))",
    ["harmonic-analysis", "kakeya"], "GOAL"))

print(f"Adding {len(items)} items...")
item_ids = []
for i, item in enumerate(items):
    name = item.get("theorem_name") or item.get("definition_name")
    print(f"[{i+1}/{len(items)}] {name}...", end=" ", flush=True)
    status, resp = api_post(f"/mission-proposals/{PROP_ID}/items", item)
    if status in (200, 201) and resp:
        item_id = resp.get("id")
        item_ids.append(item_id)
        print(f"OK ({item_id[:8]})")
    else:
        print(f"FAILED (status={status})")
        item_ids.append(None)

# Save mapping
mapping = {}
for item, iid in zip(items, item_ids):
    name = item.get("theorem_name") or item.get("definition_name")
    mapping[name] = iid

with open('/tmp/item_mapping.json', 'w') as f:
    json.dump(mapping, f, indent=2)

print(f"\nDone: {sum(1 for x in item_ids if x)}/{len(items)} succeeded")
