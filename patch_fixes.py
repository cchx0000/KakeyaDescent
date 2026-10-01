#!/usr/bin/env python3
"""PATCH proposal items: fixed definition names, new Lean code, fixed NL statements."""
import json, urllib.request, urllib.error, time, os, sys

BASE = "https://prove2.me/api/v1"
PID = "a8573c95-0003-4cd8-93c6-9e6670624d32"
TOKEN = open('/tmp/p2m_token').read().strip()
LEAN = "/home/hatch/workspace/prove2me-paper/lean"
mapping = json.load(open('/tmp/item_mapping.json'))

def read_lean(path):
    with open(os.path.join(LEAN, path)) as f:
        return f.read()

def api_patch(item_id, data, retries=4):
    url = f"{BASE}/mission-proposals/{PID}/items/{item_id}"
    body = json.dumps(data).encode()
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, data=body, headers={
                "Authorization": f"Bearer {TOKEN}",
                "Content-Type": "application/json",
            }, method="PATCH")
            with urllib.request.urlopen(req, timeout=60) as resp:
                return resp.status
        except urllib.error.HTTPError as e:
            print(f"  HTTP {e.code}: {e.read().decode()[:300]}")
            return e.code
        except Exception as e:
            print(f"  Attempt {attempt+1} failed: {type(e).__name__}")
            time.sleep(4)
    return None

updates = []

# 1. SubpowerLE: new code + new NL (uniform in delta)
updates.append(("FilteredDescent.SubpowerLE", {
    "definition": read_lean("Definitions/Def_FilteredDescent_Subpower.lean"),
    "natural_language_statement":
        "A scale-dependent quantity $x(\\delta)$ is subpower-bounded by $y(\\delta)$, "
        "written $x \\lesssim y$, if for every $\\varepsilon > 0$ there exists $C \\geq 0$ "
        "(independent of $\\delta$) with $x(\\delta) \\leq C\\, \\delta^{-\\varepsilon}\\, y(\\delta)$ "
        "for all $\\delta \\in (0,1)$. Includes the reflexivity and right-transitivity lemmas.",
}))

# 2-5. Rename definition items to real declaration names (code unchanged)
updates.append(("FilteredDescent.Packet", {
    "theorem_name": "FilteredDescent.packetLaw",
    "theorem_title": "Ordered packet law (packetLaw, slotMarginal, retainedMass)",
}))
updates.append(("FilteredDescent.Kernel", {
    "theorem_name": "FilteredDescent.margLaw",
    "theorem_title": "Slot marginal law and insertion kernels (margLaw, insKernel)",
}))
updates.append(("FilteredDescent.Tree", {
    "theorem_name": "FilteredDescent.treeLeaves",
    "theorem_title": "History tree leaves and children (treeLeaves, treeChildren)",
}))
updates.append(("FilteredDescent.Pivot", {
    "theorem_name": "FilteredDescent.gramTake",
    "theorem_title": "Leading Gram block and pivot square (gramTake, pivotSq)",
}))

# 6. Analytic -> PlanarInput: new name + new code + new NL
updates.append(("FilteredDescent.Analytic", {
    "theorem_name": "FilteredDescent.PlanarInput",
    "theorem_title": "Analytic inputs (PlanarInput, StickyInput, Marked4DInput, ShadedTubes, GateStage)",
    "definition": read_lean("Definitions/Def_FilteredDescent_Analytic.lean"),
    "natural_language_statement":
        "The three imported analytic estimates as predicates over scale-dependent data: "
        "the hereditary planar Cordoba input (H2), the sticky Kakeya input (H3), and the uniform "
        "marked 4D sticky input (H4) — each asserting a union lower bound plus a multiplicity upper "
        "bound, up to subpower losses uniform for $\\delta \\in (0,1)$. (H3) and (H4) share the same "
        "abstract quantitative shape, which is the interface the descent consumes; they are distinct "
        "assumptions (sticky $d=3$ from [7,10] vs marked $d=4$ from [9]), selected by the dimension "
        "hypothesis at use sites. Plus the `ShadedTubes` record and the `GateStage` record bundling "
        "a history tree with the tube family it is built over.",
}))

# 7-10. Theorem code updates (delta-uniform + dimension-conditional)
updates.append(("FilteredDescent.root_cross_gate", {
    "formal_statement": read_lean("Theorems/Thm_FilteredDescent_RootCrossGate.lean"),
}))
updates.append(("FilteredDescent.support_recurrence_closure", {
    "formal_statement": read_lean("Theorems/Thm_FilteredDescent_SupportRecurrence.lean"),
}))
updates.append(("FilteredDescent.terminal_incidence_count", {
    "formal_statement": read_lean("Theorems/Thm_FilteredDescent_TerminalCount.lean"),
}))
updates.append(("FilteredDescent.scalar_closure", {
    "formal_statement": read_lean("Theorems/Thm_FilteredDescent_ScalarClosure.lean"),
}))

# 11. R5: fix overstated natural language (code unchanged)
updates.append(("FilteredDescent.r5_marginal_bound", {
    "natural_language_statement":
        "For an ordered packet law, the unconditioned slot-$s$ marginal equals the base tube law "
        "$w_t/W$. Conditioning on an event $A$ of retained mass $\\alpha > 0$ keeps each slot "
        "marginal pointwise $\\leq \\alpha^{-1} \\cdot (w_t/W)$.",
}))

print(f"Patching {len(updates)} items...")
ok = 0
for name, data in updates:
    item_id = mapping[name]
    print(f"- {name} ({item_id[:8]}) fields={list(data.keys())}...", end=" ", flush=True)
    status = api_patch(item_id, data)
    if status in (200, 201):
        print("OK")
        ok += 1
    else:
        print(f"FAILED ({status})")

print(f"\nDone: {ok}/{len(updates)} patched")
