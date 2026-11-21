#!/usr/bin/env python3
"""Task 4.1 — independent leanchecker + #print axioms replay of the 173 distinct
infinite-map certificates. Three facts per cert, none trusting the judge's own
axiom report: (a) judge zero-policy verdict, (b) leanchecker exit code (kernel
re-check of the proof term), (c) my own `#print axioms submission`.
"""
import json, hashlib, os, subprocess, sys, glob, concurrent.futures as cf, time

CLONE = "/Volumes/Crucial_X9/scratch/math/stage2-judge/equational-theories-lean-stage2"
PF    = "/Users/carlo/Documents/varie/hacks/lean4/packed-footprint-lean"
RUN   = "/Volumes/Crucial_X9/scratch/math/stage2-judge/run41"
LEAN  = os.path.expanduser("~/.elan/bin/lean")
LAKE  = os.path.expanduser("~/.elan/bin/lake")
LEANCHK = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/leanchecker")

roots = [f"{CLONE}/.lake/build/lib/lean"] + sorted(glob.glob(f"{CLONE}/.lake/packages/*/.lake/build/lib/lean"))
JLP = ":".join(roots)

def log(m): print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)

# --- dedup by code ---
certs = json.load(open(f"{PF}/infinite-map/certificates.json"))
seen, specs = {}, []
for e in certs:
    h = hashlib.sha256(e["code"].encode()).hexdigest()
    if h in seen:
        continue
    seen[h] = e["id"]
    specs.append(e)
json.dump(specs, open(f"{RUN}/specs-173.json", "w"))
log(f"{len(certs)} entries -> {len(specs)} distinct codes")

# --- stage A: judge, zero policy, keep artifacts ---
env = dict(os.environ, JUDGE_LEAN_PATH=JLP, LEAN_BIN=LEAN, LAKE_BIN=LAKE)
log("stage A: cert_run.py zero --keep")
subprocess.run([sys.executable, f"{PF}/cert_run.py", "--judge", CLONE,
    "--input", f"{RUN}/specs-173.json", "--policy", "zero", "--verdict", "false",
    "--out", f"{RUN}/judge.jsonl", "--artifacts", f"{RUN}/artifacts",
    "--keep", "--workers", "4"], env=env, cwd=PF, check=True)
judge = {}
for line in open(f"{RUN}/judge.jsonl"):
    r = json.loads(line)
    judge[r["id"]] = r

# --- stage B: leanchecker + independent #print axioms ---
dirs = sorted(glob.glob(f"{RUN}/artifacts/zero/*/"))
log(f"stage B: leanchecker + #print axioms over {len(dirs)} artifacts")

def check(d):
    d = d.rstrip("/")
    cid = os.path.basename(d).split(".")[0]
    e2 = dict(os.environ, LEAN_PATH=d + ":" + JLP)
    out = {"id": cid, "dir": os.path.basename(d)}
    try:
        lc = subprocess.run([LEANCHK, "Submission"], env=e2, capture_output=True, text=True, timeout=600)
        out["leanchecker_exit"] = lc.returncode
        out["leanchecker_err"] = (lc.stderr or "").strip()[:300]
    except Exception as ex:
        out["leanchecker_exit"] = -1
        out["leanchecker_err"] = f"{type(ex).__name__}: {ex}"[:300]
    chk = f"{d}/chk.lean"
    open(chk, "w").write("import Submission\n#print axioms submission\n")
    try:
        pa = subprocess.run([LEAN, chk], env=e2, capture_output=True, text=True, timeout=600)
        line = (pa.stdout or "").strip()
        out["print_axioms"] = line[:300]
        out["no_axioms"] = "does not depend on any axioms" in line
        out["print_axioms_exit"] = pa.returncode
    except Exception as ex:
        out["print_axioms"] = f"{type(ex).__name__}: {ex}"[:300]
        out["no_axioms"] = False
        out["print_axioms_exit"] = -1
    jr = judge.get(cid, {})
    out["judge_status"] = jr.get("status")
    out["judge_axioms"] = jr.get("axioms")
    out["bytes"] = jr.get("bytes")
    return out

rows = []
with cf.ThreadPoolExecutor(4) as pool:
    for i, r in enumerate(pool.map(check, dirs), 1):
        rows.append(r)
        bad = (r["leanchecker_exit"] != 0) or (not r["no_axioms"]) or (r["judge_status"] != "accepted")
        if i % 25 == 0 or bad:
            log(f"{i}/{len(dirs)} {r['id']} judge={r['judge_status']} "
                f"lc={r['leanchecker_exit']} no_axioms={r['no_axioms']}")

rows.sort(key=lambda r: r["id"])
with open(f"{RUN}/results.jsonl", "w") as fh:
    for r in rows:
        fh.write(json.dumps(r, ensure_ascii=False) + "\n")

summary = {
    "distinct_certs": len(rows),
    "judge_accepted_zero": sum(r["judge_status"] == "accepted" for r in rows),
    "leanchecker_exit0": sum(r["leanchecker_exit"] == 0 for r in rows),
    "independent_no_axioms": sum(bool(r["no_axioms"]) for r in rows),
    "all_three_agree": sum((r["judge_status"] == "accepted") and (r["leanchecker_exit"] == 0) and r["no_axioms"] for r in rows),
    "failures": [r for r in rows if (r["leanchecker_exit"] != 0) or (not r["no_axioms"]) or (r["judge_status"] != "accepted")],
    "judge_commit": "817a4653bf762584931d49c6714c9fcfab7df66a",
    "lean": "4.33.1",
    "policy": "zero (allowed_axioms=[])",
}
json.dump(summary, open(f"{RUN}/summary-41.json", "w"), indent=2)
log("SUMMARY " + json.dumps({k: v for k, v in summary.items() if k != "failures"}))
log(f"failures: {len(summary['failures'])}")
