#!/usr/bin/env python3
"""Extract read-back texts from auditor agent sessions."""
import json, os

# agent_id -> (item_name, description)
agents = {
    "ff864ade-b3e8-4d55-adf8-991a37687a9a": "FilteredDescent.SubpowerLE",
    "63aeca21-8238-43ec-922b-0c09adcf34e8": "FilteredDescent.Packet",
    "4e5a8b13-70e3-445f-8d78-e0963d38101c": "FilteredDescent.Kernel",
    "ba08aa50-5bd1-4f0b-9ed5-c43123d78986": "FilteredDescent.Tree",
    "f18e87d9-faec-4bbe-af04-83b4cac1bc1b": "FilteredDescent.Pivot",
    "74a90d08-e69b-41a9-a5cd-42c946cf336d": "FilteredDescent.Analytic",
    "afcfb110-08fa-4d32-86c6-48bebc9c2b2f": "FilteredDescent.r5_marginal_bound",
    "5611ef2d-b269-4e39-9f99-41d5ef6a92be": "FilteredDescent.ordered_cauchy_binet",
    "45815574-05f8-4379-afb2-b04a16ea8eb2": "FilteredDescent.kernel_chain_confluence",
    "72fa4ca3-d81c-4059-b6d8-7d6d602c999b": "FilteredDescent.pivot_dichotomy",
    "dc8e3508-d305-48ce-b89e-cd1e3e13b532": "FilteredDescent.tree_lca_reduction",
    "ee82aaae-b2ed-46d5-a943-82facafada14": "FilteredDescent.duplicate_closure",
    "cadeec03-3fd8-463e-986a-21a5cf409343": "FilteredDescent.r5_insufficiency_model",
    "b873ac85-459e-4539-891f-d0ffc1ae57b8": "FilteredDescent.root_cross_gate",
    "d2cd1a07-006c-48d9-b677-0c176b3c9e5b": "FilteredDescent.support_recurrence_closure",
    "4d05f8ae-f172-4221-b7d3-913c0f63a57f": "FilteredDescent.terminal_incidence_count",
    "f4bb87ff-01c2-4e48-9df9-9ae64c621efb": "FilteredDescent.unweighted_projection_false",
    "da18ca6b-23d4-4a67-9eb5-7109ca299350": "FilteredDescent.scalar_closure",
}

outdir = "/home/hatch/workspace/prove2me-paper/readbacks"
os.makedirs(outdir, exist_ok=True)

results = {}
for aid, name in agents.items():
    path = f"/home/hatch/agents/agent-{aid}/sessions/{aid}.jsonl"
    try:
        with open(path) as f:
            lines = [json.loads(l) for l in f]
        # Find the last assistant message with text
        text = None
        for line in reversed(lines):
            item = line.get('item', {})
            if item.get('type') == 'message' and item.get('role') == 'assistant':
                t = item.get('text', '')
                if t and len(t) > 200:
                    text = t
                    break
        if text:
            # Save to file
            safe = name.replace('.', '_')
            with open(f"{outdir}/{safe}.md", 'w') as f:
                f.write(text)
            results[name] = len(text)
            print(f"OK {name}: {len(text)} chars")
        else:
            print(f"MISSING {name}: no text found")
            results[name] = 0
    except Exception as e:
        print(f"ERROR {name}: {e}")
        results[name] = 0

print(f"\nExtracted {sum(1 for v in results.values() if v > 0)}/{len(agents)}")
