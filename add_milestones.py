#!/usr/bin/env python3
"""Create 11 milestones (one per theorem, goal excluded)."""
import json, urllib.request, urllib.error, time

TOKEN = open('/tmp/p2m_token').read().strip()
PROP_ID = open('/tmp/proposal_id').read().strip()
BASE = "https://prove2.me/api/v1"

mapping = json.load(open('/tmp/item_mapping.json'))

milestones = [
    ("FilteredDescent.r5_marginal_bound",
     "M1 — R5 marginal bound (9), (25)",
     "Conditioning an ordered packet law on an event of retained mass $\\alpha > 0$ preserves each slot marginal up to the factor $\\alpha^{-1}$. This is the paper's R5: the single-slot estimate that seeds the whole descent. Prove the exact equality of conditioned and unconditioned marginals first, then the $\\alpha^{-1}$ domination."),
    ("FilteredDescent.ordered_cauchy_binet",
     "M2 — Ordered Cauchy–Binet packet identity (6)",
     "The weighted sum of squared determinants over ordered $d$-tuples equals $d!$ times the weighted Gram determinant. This is the packet-level linear algebra: it converts packet sums into Gram determinants that the pivot dichotomy (M4) can attack. Differs from the platform's subset-sum Cauchy–Binet by the ordered-tuple (not subset) indexing."),
    ("FilteredDescent.kernel_chain_confluence",
     "M3 — Insertion kernels (13)–(16)",
     "The chain rule for nested slot sets and confluence of two-slot insertion order. These kernels are the descent's bookkeeping: they let later stages insert new slots without disturbing the already-filtered law."),
    ("FilteredDescent.pivot_dichotomy",
     "M4 — Gram–Schmidt pivot dichotomy (32)–(42)",
     "Pivot product identity, the broad/narrow dichotomy, and the broad-case determinant lower bound $\\kappa^{2r}$. The narrow case feeds the induction; the broad case is where the analytic input bites."),
    ("FilteredDescent.tree_lca_reduction",
     "M5 — History-tree LCA reduction (131)–(141)",
     "Splitting the leaf-pair mass by least common ancestor reduces the $L^2/L^1$ estimate to the root-cross term $X^{\\mathrm{root}}$ plus $D \\cdot B \\cdot \\int N$ from the $\\leq D$ proper levels. The finite form of the paper's $H_{I,k} = \\delta^{-o(1)}$ height factor."),
    ("FilteredDescent.duplicate_closure",
     "M6a — Common-source duplicate closure (143)–(155)",
     "$X^{\\mathrm{root}} = X^{\\mathrm{geom}} + X^{\\mathrm{dup}}$ exactly; the duplicate part (pairs sharing a terminal tube) is closed by the per-carrier aggregate bound. This is the unconditional half of the root-cross gate."),
    ("FilteredDescent.r5_insufficiency_model",
     "M6b — R5 insufficiency model (§10.5)",
     "The paper's one-point model showing chartwise R5 does NOT imply the duplicate bound: $R$ unit-mass histories in one tube give $X^{\\mathrm{root}} = R^2 - R$ with no $R$-independent estimate. A negative result — prove it to certify the duplicate closure (M6a) is doing real work."),
    ("FilteredDescent.root_cross_gate",
     "M7 — Root-cross gate (142), d = 2, 3, 4",
     "The conditional heart: $X^{\\mathrm{root}} \\lesssim_\\delta B^{\\mathrm{pred}} \\cdot \\int N$, from M6a plus the per-dimension analytic assembly. Takes the three imported estimates (planar Córdoba [2], sticky Kakeya [7,10], marked 4D sticky [9]) as explicit hypotheses. $d \\geq 5$ is out of scope."),
    ("FilteredDescent.support_recurrence_closure",
     "M8a — Closed support recurrence (124)–(125)",
     "Strong induction on $|I|$: the base case $|I| \\leq 2$ plus the support-step recurrence closes the descent, giving $B_I \\lesssim_\\delta 1$ for all supports."),
    ("FilteredDescent.terminal_incidence_count",
     "M8b — Terminal incidence count (130) → (214)",
     "The terminal unweighting converts retained mass and multiplicity (both subpower) into the incidence count $\\sum_T |Y(T)| \\lesssim_\\delta |\\bigcup_T Y(T)|$."),
    ("FilteredDescent.unweighted_projection_false",
     "M9 — Unweighted projection is false (54)",
     "Counterexample: conditioning does not preserve slot marginals (concrete $1 \\neq 1/2$). A negative result certifying that R5's $\\alpha^{-1}$ factor is necessary, not an artifact."),
]

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
            print(f"  HTTP {e.code}: {e.read().decode()[:600]}")
            return e.code, None
        except Exception as e:
            print(f"  Attempt {attempt+1} failed: {e}")
            time.sleep(2)
    return None, None

print(f"Creating {len(milestones)} milestones...")
for i, (name, title, desc) in enumerate(milestones):
    item_id = mapping[name]
    print(f"[{i+1}/{len(milestones)}] {title[:40]}...", end=" ", flush=True)
    status, resp = api_post(f"/mission-proposals/{PROP_ID}/milestones", {
        "item_id": item_id,
        "milestone_title": title,
        "milestone_description": desc,
    })
    if status in (200, 201):
        print("OK")
    else:
        print(f"FAILED ({status})")

print("Done.")
