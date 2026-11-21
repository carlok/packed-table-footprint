#!/usr/bin/env python3
"""Step 4b: replay the 173 distinct infinite-map certificates under toolchains that
contain the upstream kernel fix (4.34.1, 4.35.0). The import chain is
JudgeMagma.Magma (no imports) -> JudgeProblem -> Submission, so plain `lean` is enough:
no Mathlib, no judge build. Per certificate and toolchain: compile, leanchecker,
leanchecker-paranoid (where the toolchain ships it), an independent #print axioms,
and a check that `submission : Goal` still typechecks. Also a toolchain-independent
scan of each Submission.lean for meta-level constructs.
"""
import argparse, concurrent.futures as cf, glob, json, os, re, shutil, subprocess, time

J = "/Volumes/Crucial_X9/scratch/math/stage2-judge/equational-theories-lean-stage2/judge"
ART = "/Volumes/Crucial_X9/scratch/math/stage2-judge/run41/artifacts/zero"
OUT = "/Volumes/Crucial_X9/scratch/math/stage2-judge/run4b"
TCROOT = os.path.expanduser("~/.elan/toolchains")

ap = argparse.ArgumentParser()
ap.add_argument("--toolchains", default="v4.34.1,v4.35.0")
ap.add_argument("--limit", type=int, default=0)
ap.add_argument("--workers", type=int, default=4)
ap.add_argument("--tag", default="full")
args = ap.parse_args()


def log(m):
    print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)


def run(cmd, cwd, env_extra, timeout):
    env = dict(os.environ)
    env.update(env_extra)
    try:
        p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return 124, "", "timeout"
    except Exception as ex:
        return -1, "", f"{type(ex).__name__}: {ex}"


dirs = sorted(glob.glob(f"{ART}/*/"))
if args.limit:
    dirs = dirs[: args.limit]
log(f"{len(dirs)} artifact directories")

# --- toolchain-independent scan for meta-level constructs ---
SCAN = {
    "unsafe": r"\bunsafe\b", "implemented_by": r"implemented_by", "extern": r"\bextern\b",
    "macro": r"\bmacro\b", "syntax": r"\bsyntax\b", "elab": r"\belab\b",
    "initialize": r"\binitialize\b", "run_": r"\brun_[a-z_]+", "import_Lean": r"\bimport\s+Lean\b",
    "open_Lean": r"\bopen\s+Lean\b", "attr": r"@\[", "native_decide": r"\bnative_decide\b",
    "sorry": r"\bsorry\b", "partial": r"\bpartial\b", "opaque": r"\bopaque\b", "axiom": r"\baxiom\b",
    "set_option": r"\bset_option\b",
}
scan_counts = {k: 0 for k in SCAN}
scan_files = {k: [] for k in SCAN}
for d in dirs:
    text = open(f"{d}/Submission.lean", encoding="utf-8").read()
    cid = os.path.basename(d.rstrip("/"))
    for k, pat in SCAN.items():
        if re.search(pat, text):
            scan_counts[k] += 1
            if len(scan_files[k]) < 5:
                scan_files[k].append(cid)
log("scan counts (files with at least one hit): " + json.dumps({k: v for k, v in scan_counts.items() if v}))

summary = {"artifacts": len(dirs), "scan_counts": scan_counts,
           "scan_examples": {k: v for k, v in scan_files.items() if v}, "toolchains": {}}


def do_toolchain(T):
    bindir = f"{TCROOT}/leanprover--lean4---{T}/bin"
    lean, chk, para = f"{bindir}/lean", f"{bindir}/leanchecker", f"{bindir}/leanchecker-paranoid"
    have_para = os.path.exists(para)
    tcenv = {"PATH": bindir + ":" + os.environ["PATH"],
             "LEAN_SYSROOT": f"{TCROOT}/leanprover--lean4---{T}"}
    ver = run([lean, "--version"], J, tcenv, 30)[1].strip()
    log(f"{T}: {ver} paranoid={'yes' if have_para else 'no'}")
    root = f"{OUT}/{args.tag}/{T}"
    shutil.rmtree(root, ignore_errors=True)
    common = f"{root}/common"
    os.makedirs(f"{common}/JudgeMagma")
    rc, so, se = run([lean, "JudgeMagma/Magma.lean", "-o", f"{common}/JudgeMagma/Magma.olean"], J, tcenv, 300)
    if rc != 0:
        log(f"{T}: JudgeMagma.Magma failed to compile: {(so + se)[:300]}")
        return {"version": ver, "error": "JudgeMagma.Magma failed"}

    def one(d):
        base = os.path.basename(d.rstrip("/"))
        work = f"{root}/certs/{base}"
        os.makedirs(work, exist_ok=True)
        for f in ("JudgeProblem.lean", "Submission.lean"):
            shutil.copy(f"{d}/{f}", f"{work}/{f}")
        lp = f"{common}:{work}"
        r = {"id": base.split(".")[0], "dir": base, "toolchain": T}
        rc, so, se = run([lean, "JudgeProblem.lean", "-o", "JudgeProblem.olean"], work, {"LEAN_PATH": lp, **tcenv}, 300)
        r["problem_compile"] = rc
        if rc != 0:
            r["err"] = (so + se)[:300]
            return r
        rc, so, se = run([lean, "Submission.lean", "-o", "Submission.olean"], work, {"LEAN_PATH": lp, **tcenv}, 600)
        r["submission_compile"] = rc
        if rc != 0:
            r["err"] = (so + se)[:300]
            return r
        rc, so, se = run([chk, "Submission"], work, {"LEAN_PATH": lp, **tcenv}, 600)
        r["leanchecker"] = rc
        r["leanchecker_out"] = (so + se).strip()[:200]
        if have_para:
            rc, so, se = run([para, "Submission"], work, {"LEAN_PATH": lp, **tcenv}, 600)
            r["paranoid"] = rc
            r["paranoid_out"] = (so + se).strip()[:200]
        open(f"{work}/chk.lean", "w").write("import Submission\n#print axioms submission\n#check (submission : Goal)\n")
        rc, so, se = run([lean, "chk.lean"], work, {"LEAN_PATH": lp, **tcenv}, 300)
        r["chk_exit"] = rc
        r["no_axioms"] = "does not depend on any axioms" in so
        r["goal_ok"] = rc == 0 and "Goal" in so
        return r

    rows = []
    with cf.ThreadPoolExecutor(args.workers) as pool:
        for i, r in enumerate(pool.map(one, dirs), 1):
            rows.append(r)
            bad = (r.get("submission_compile") != 0 or r.get("leanchecker") != 0 or
                   (have_para and r.get("paranoid") != 0) or not r.get("no_axioms") or not r.get("goal_ok"))
            if bad or i % 25 == 0:
                log(f"{T} {i}/{len(dirs)} {r['id']} compile={r.get('submission_compile')} lc={r.get('leanchecker')} "
                    f"para={r.get('paranoid')} no_axioms={r.get('no_axioms')} goal={r.get('goal_ok')}")
    rows.sort(key=lambda r: r["id"])
    with open(f"{OUT}/results-{args.tag}-{T}.jsonl", "w") as fh:
        for r in rows:
            fh.write(json.dumps(r, ensure_ascii=False) + "\n")
    ok = [r for r in rows if r.get("submission_compile") == 0 and r.get("leanchecker") == 0
          and (not have_para or r.get("paranoid") == 0) and r.get("no_axioms") and r.get("goal_ok")]
    return {"version": ver, "paranoid_available": have_para, "certificates": len(rows),
            "compiled": sum(r.get("submission_compile") == 0 for r in rows),
            "leanchecker_exit0": sum(r.get("leanchecker") == 0 for r in rows),
            "paranoid_exit0": sum(r.get("paranoid") == 0 for r in rows) if have_para else None,
            "independent_no_axioms": sum(bool(r.get("no_axioms")) for r in rows),
            "goal_typechecks": sum(bool(r.get("goal_ok")) for r in rows),
            "all_checks_pass": len(ok),
            "failures": [r for r in rows if r not in ok][:10]}


for T in args.toolchains.split(","):
    summary["toolchains"][T] = do_toolchain(T)
    log(f"{T} summary: " + json.dumps({k: v for k, v in summary["toolchains"][T].items() if k != "failures"}))

json.dump(summary, open(f"{OUT}/summary-4b-{args.tag}.json", "w"), indent=2)
log("done")
