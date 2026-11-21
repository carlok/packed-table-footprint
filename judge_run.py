#!/usr/bin/env python3
"""Run false-verdict certificates through the competition's own judge, in several
encodings of the same operation.

    table   finOpTable on a string, as published
    packed  one Nat literal, read back with tbl / n ^ (x * n + y) % n
    list    a List Nat literal, read back with List.getD
    nth     the same literal, read back with a hand-written structural lookup

The goal, the tactic and the options are untouched. Only the operation changes.
Policies are the runner's DEFAULT_PROOF_POLICY ("official") and the same policy
with no axioms allowed ("zero").

    judge_run.py --judge CLONE --input SPECS.json --plan table:official,packed:zero
                 --out OUT.jsonl --artifacts DIR [--workers N]

Needs JUDGE_LEAN_PATH (the four Judge* modules, built from the clone), LEAN_BIN and
LAKE_BIN in the environment. OUT is appended to, and finished rows are skipped, so a
run can be resumed.
"""
import argparse
import concurrent.futures as cf
import json
import os
import re
import shutil
import sys
import threading
import time
import types
from pathlib import Path


def table_of(code):
    return json.loads(re.search(r'finOpTable "(\[\[.*?\]\])"', code).group(1))


def body_tail(code):
    """Everything from the set_option lines on, with `op` left open."""
    m = re.search(r"((?:set_option [^\n]*\n)*def submission : Goal := by\n.*)", code, re.S)
    return re.sub(r'op := finOpTable "\[\[.*?\]\]"', "op := submission.op", m.group(1))


def encode(code, enc):
    if enc == "table":
        return code
    t = table_of(code)
    n = len(t)
    flat = ", ".join(str(v) for row in t for v in row)
    if enc == "packed":
        tbl = sum(t[i][j] * n ** (n * i + j) for i in range(n) for j in range(n))
        defs = (f"def tbl : Nat := {tbl}\n"
                f"def op (x y : Fin {n}) : Fin {n} := "
                f"⟨(tbl / {n} ^ (x.val * {n} + y.val)) % {n}, Nat.mod_lt _ (by decide)⟩\n")
    elif enc == "list":
        defs = (f"def tbl : List Nat := [{flat}]\n"
                f"def op (x y : Fin {n}) : Fin {n} := "
                f"⟨(tbl.getD (x.val * {n} + y.val) 0) % {n}, Nat.mod_lt _ (by decide)⟩\n")
    elif enc == "nth":
        defs = (f"def tbl : List Nat := [{flat}]\n"
                "def nth : List Nat → Nat → Nat\n"
                "  | [], _ => 0\n  | a :: _, 0 => a\n  | _ :: l, k + 1 => nth l k\n"
                f"def op (x y : Fin {n}) : Fin {n} := "
                f"⟨(nth tbl (x.val * {n} + y.val)) % {n}, Nat.mod_lt _ (by decide)⟩\n")
    else:
        raise ValueError(enc)
    return ("import JudgeProblem\nimport JudgeDecide.DecideBang\n\n"
            "namespace submission\n" + defs + "end submission\n\n" + body_tail(code))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--judge", required=True)
    ap.add_argument("--input", required=True)
    ap.add_argument("--plan", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--artifacts", required=True)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--only")
    args = ap.parse_args()

    sys.path.insert(0, str(Path(args.judge).resolve()))
    sys.modules.setdefault("openai", types.SimpleNamespace(OpenAI=object))
    from judge.verify import JudgeConfig, verify_answer
    from pipeline.proxy import DEFAULT_PROOF_POLICY

    policies = {"official": DEFAULT_PROOF_POLICY,
                "zero": {**DEFAULT_PROOF_POLICY, "allowed_axioms": []}}
    assert set(DEFAULT_PROOF_POLICY["allowed_axioms"]) == {"propext", "Quot.sound", "Classical.choice"}

    specs = json.loads(Path(args.input).read_text(encoding="utf-8"))
    if args.only:
        wanted = set(args.only.split(","))
        specs = [s for s in specs if s["id"] in wanted]
    plan = [tuple(p.split(":")) for p in args.plan.split(",")]

    out = Path(args.out)
    done = set()
    if out.exists():
        for line in out.read_text(encoding="utf-8").splitlines():
            r = json.loads(line)
            done.add((r["id"], r["enc"], r["policy"]))
    jobs = [(s, enc, pol) for s in specs for enc, pol in plan if (s["id"], enc, pol) not in done]
    print(f"{len(specs)} specs, {len(jobs)} judge calls to do, {len(done)} already done", flush=True)

    # The judge's artifact folder is keyed on problem and answer, not on policy, so two
    # policies on one certificate must not share a root.
    configs = {pol: JudgeConfig(lean_bin=Path(os.environ["LEAN_BIN"]), lake_bin=Path(os.environ["LAKE_BIN"]),
                                artifact_dir=Path(args.artifacts).resolve() / pol) for pol in policies}
    lock = threading.Lock()

    def run(job):
        spec, enc, pol = job
        code = encode(spec["code"], enc)
        problem = {k: spec[k] for k in ("id", "eq1_id", "eq2_id", "equation1", "equation2")}
        problem["proof_policy"] = policies[pol]
        start = time.monotonic()
        try:
            res = verify_answer(problem, json.dumps({"verdict": "false", "code": code}), config=configs[pol])
        except Exception as exc:  # recorded as a row, so that one failure cannot lose the run
            res = {"status": "infrastructure_error", "error_code": type(exc).__name__, "message": str(exc)}
        row = {"id": spec["id"], "enc": enc, "policy": pol, "n": len(table_of(spec["code"])),
               "status": res.get("status"), "error_code": res.get("error_code"),
               "axioms": res.get("axioms"), "direct_declarations": res.get("direct_declarations"),
               "seconds": round(time.monotonic() - start, 2), "bytes": len(code.encode("utf-8")),
               "message": (res.get("message") or "")[:300] if res.get("status") != "accepted" else None}
        art = res.get("artifact_path")
        if art:
            shutil.rmtree(art, ignore_errors=True)
        with lock:
            with out.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(row, ensure_ascii=False) + "\n")
        return row

    with cf.ThreadPoolExecutor(args.workers) as pool:
        for i, row in enumerate(pool.map(run, jobs), 1):
            if i % 50 == 0 or row["status"] != "accepted":
                print(f"{i}/{len(jobs)} {row['id']} {row['enc']}:{row['policy']} n={row['n']} {row['status']} "
                      f"{row['error_code']} axioms={row['axioms']} {row['seconds']}s", flush=True)
    print("finished", flush=True)


if __name__ == "__main__":
    main()
