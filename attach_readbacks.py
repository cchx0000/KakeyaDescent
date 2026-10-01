#!/usr/bin/env python3
"""Attach read-backs to proposal items via PATCH."""
import json, urllib.request, urllib.error, time, os

TOKEN = open('/tmp/p2m_token').read().strip()
PROP_ID = open('/tmp/proposal_id').read().strip()
BASE = "https://prove2.me/api/v1"
READBACK_DIR = "/home/hatch/workspace/prove2me-paper/readbacks"

mapping = json.load(open('/tmp/item_mapping.json'))

# The model that wrote the read-backs (the auditor sub-agents)
READBACK_MODEL = "muse-spark"

def api_patch(path, data, retries=4):
    url = BASE + path
    body = json.dumps(data).encode()
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, data=body, headers={
                "Authorization": f"Bearer {TOKEN}",
                "Content-Type": "application/json",
            }, method="PATCH")
            with urllib.request.urlopen(req, timeout=60) as resp:
                return resp.status, json.load(resp)
        except urllib.error.HTTPError as e:
            print(f"  HTTP {e.code}: {e.read().decode()[:500]}")
            return e.code, None
        except Exception as e:
            print(f"  Attempt {attempt+1} failed: {e}")
            time.sleep(3)
    return None, None

names = list(mapping.keys())
print(f"Patching {len(names)} items with read-backs...")
success = 0
for i, name in enumerate(names):
    item_id = mapping[name]
    safe = name.replace('.', '_')
    rb_path = f"{READBACK_DIR}/{safe}.md"
    if not os.path.exists(rb_path):
        print(f"[{i+1}/{len(names)}] {name}: NO READBACK FILE, skipping")
        continue
    with open(rb_path) as f:
        readback = f.read()
    print(f"[{i+1}/{len(names)}] {name} ({len(readback)} chars)...", end=" ", flush=True)
    status, resp = api_patch(
        f"/mission-proposals/{PROP_ID}/items/{item_id}",
        {"readback": readback, "readback_model": READBACK_MODEL}
    )
    if status in (200, 201):
        print("OK")
        success += 1
    else:
        print(f"FAILED ({status})")

print(f"\nDone: {success}/{len(names)} read-backs attached")
