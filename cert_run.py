#!/usr/bin/env python3
"""Run certificates through verify_answer verbatim, for either verdict, following judge_run.py
in everything except the re-encoding (none here) and the verdict (a flag, or per-spec).

    cert_run.py --judge CLONE --input SPECS.json --policy zero --verdict true --out OUT.jsonl
                --artifacts DIR [--workers N] [--only id,id] [--keep]

Policies: official = runner's DEFAULT_PROOF_POLICY; zero = the same with allowed_axioms=[];
default = no proof_policy key at all, so the judge's own default applies (no axioms, no
declaration check). Needs JUDGE_LEAN_PATH, LEAN_BIN, LAKE_BIN. OUT is appended to and finished
rows are skipped, so a run can be resumed. With --keep the artifact folder (Submission.olean,
the sources) stays, for the constant walk.
"""
import argparse
import concurrent.futures as cf
import json
import os
import shutil
import sys
import threading
import time
import types
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--judge", required=True)
    ap.add_argument("--input", required=True)
    ap.add_argument("--policy", required=True, choices=["official", "zero", "default"])
    ap.add_argument("--verdict", default=None)
    ap.add_argument("--out", required=True)
    ap.add_argument("--artifacts", required=True)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--only")
    ap.add_argument("--keep", action="store_true")
    args = ap.parse_args()

    sys.path.insert(0, str(Path(args.judge).resolve()))
    sys.modules.setdefault("openai", types.SimpleNamespace(OpenAI=object))
    from judge.verify import JudgeConfig, verify_answer
    from pipeline.proxy import DEFAULT_PROOF_POLICY

    assert set(DEFAULT_PROOF_POLICY["allowed_axioms"]) == {"propext", "Quot.sound", "Classical.choice"}
    policy = {"official": DEFAULT_PROOF_POLICY,
              "zero": {**DEFAULT_PROOF_POLICY, "allowed_axioms": []},
              "default": None}[args.policy]

    specs = json.loads(Path(args.input).read_text(encoding="utf-8"))
    if args.only:
        wanted = set(args.only.split(","))
        specs = [s for s in specs if s["id"] in wanted]

    out = Path(args.out)
    done = set()
    if out.exists():
        for line in out.read_text(encoding="utf-8").splitlines():
            r = json.loads(line)
            done.add((r["id"], r["policy"]))
    jobs = [s for s in specs if (s["id"], args.policy) not in done]
    print(f"{len(specs)} specs, {len(jobs)} judge calls to do, {len(done)} already done", flush=True)

    config = JudgeConfig(lean_bin=Path(os.environ["LEAN_BIN"]), lake_bin=Path(os.environ["LAKE_BIN"]),
                         artifact_dir=Path(args.artifacts).resolve() / args.policy,
                         lean_timeout_seconds=int(os.environ.get("CERT_RUN_TIMEOUT", "300")))
    lock = threading.Lock()

    def run(spec):
        verdict = args.verdict or spec["verdict"]
        problem = {k: spec[k] for k in ("id", "eq1_id", "eq2_id", "equation1", "equation2")}
        if policy is not None:
            problem["proof_policy"] = policy
        start = time.monotonic()
        try:
            res = verify_answer(problem, json.dumps({"verdict": verdict, "code": spec["code"]}), config=config)
        except Exception as exc:  # recorded as a row, so that one failure cannot lose the run
            res = {"status": "infrastructure_error", "error_code": type(exc).__name__, "message": str(exc)}
        row = {"id": spec["id"], "verdict": verdict, "policy": args.policy, "weight": spec.get("weight", 1),
               "status": res.get("status"), "error_code": res.get("error_code"),
               "axioms": res.get("axioms"), "direct_declarations": res.get("direct_declarations"),
               "seconds": round(time.monotonic() - start, 2), "bytes": len(spec["code"].encode("utf-8")),
               "message": (res.get("message") or "")[:400] if res.get("status") != "accepted" else None}
        art = res.get("artifact_path")
        if art and not args.keep:
            shutil.rmtree(art, ignore_errors=True)
        with lock:
            with out.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(row, ensure_ascii=False) + "\n")
        return row

    with cf.ThreadPoolExecutor(args.workers) as pool:
        for i, row in enumerate(pool.map(run, jobs), 1):
            if i % 100 == 0 or row["status"] != "accepted":
                print(f"{i}/{len(jobs)} {row['id']} {row['policy']} {row['status']} {row['error_code']} "
                      f"axioms={row['axioms']} {row['seconds']}s", flush=True)
    print("finished", flush=True)


if __name__ == "__main__":
    main()
