#!/usr/bin/env python3
"""Turn judge_run.py output into the published summaries.

    summarize.py CORPUS.jsonl LEDGER.jsonl LEDGER_SPECS.json LEDGER_STATS.json OUT_DIR

This script keeps row-level results for the published certificates only. The ledger
belongs to Ma, Zhang and Cázares, and its summary is aggregate.
"""
import collections
import json
import statistics as st
import sys
from pathlib import Path


def load(path):
    return [json.loads(line) for line in Path(path).read_text(encoding="utf-8").splitlines()]


def stats(rows):
    secs = [r["seconds"] for r in rows]
    return {"calls": len(rows),
            "status": dict(collections.Counter(f'{r["status"]}/{r["error_code"]}' for r in rows)),
            "axioms": {", ".join(a) or "none": c
                       for a, c in collections.Counter(tuple(r["axioms"] or []) for r in rows).items()},
            "seconds_median": round(st.median(secs), 2), "seconds_max": max(secs),
            "seconds_total": round(sum(secs), 1),
            "bytes_median": st.median(r["bytes"] for r in rows), "bytes_max": max(r["bytes"] for r in rows)}


def by_plan(rows):
    plan = collections.defaultdict(list)
    for r in rows:
        plan[(r["enc"], r["policy"])].append(r)
    return {f"{e}:{p}": stats(v) for (e, p), v in sorted(plan.items())}


def main():
    corpus = load(sys.argv[1])
    ledger = load(sys.argv[2])
    specs = {s["id"]: s for s in json.loads(Path(sys.argv[3]).read_text(encoding="utf-8"))}
    extraction = json.loads(Path(sys.argv[4]).read_text())
    out = Path(sys.argv[5])

    rows = sorted(({k: r[k] for k in ("id", "enc", "policy", "n", "status", "error_code", "axioms", "seconds", "bytes")}
                   for r in corpus), key=lambda r: (r["id"], r["enc"], r["policy"]))
    (out / "judge-corpus.json").write_text("[\n" + ",\n".join(json.dumps(r) for r in rows) + "\n]\n")
    corpus_summary = by_plan(corpus)

    decls = collections.defaultdict(set)
    for r in corpus + ledger:
        decls[r["enc"]].update(r["direct_declarations"] or [])

    carrier = collections.defaultdict(lambda: collections.defaultdict(list))
    for r in ledger:
        carrier[r["n"]][f'{r["enc"]}:{r["policy"]}'].append(r)
    per_carrier = {
        n: {plan: {"certificates": len(v), "accepted": sum(x["status"] == "accepted" for x in v),
                   "seconds_median": round(st.median(x["seconds"] for x in v), 2),
                   "seconds_max": max(x["seconds"] for x in v)}
            for plan, v in sorted(plans.items())}
        for n, plans in sorted(carrier.items())}
    weighted = collections.Counter()
    for r in ledger:
        if r["status"] == "accepted":
            weighted[f'{r["enc"]}:{r["policy"]}'] += specs[r["id"]]["weight"]
    paired = {}
    for r in ledger:
        paired.setdefault(r["id"], {})[r["enc"]] = r["seconds"]
    ratios = [p["table"] / p["packed"] for p in paired.values() if "table" in p and "packed" in p]

    summary = {
        "judge_commit": "817a4653bf762584931d49c6714c9fcfab7df66a",
        "ledger_commit": "4bf87e3",
        "extraction": extraction,
        "plans": by_plan(ledger),
        "accepted_counting_duplicates": dict(weighted),
        "per_carrier": per_carrier,
        "table_over_packed_seconds": {"median": round(st.median(ratios), 2), "min": round(min(ratios), 2),
                                      "max": round(max(ratios), 2), "packed_slower_in": sum(x < 1 for x in ratios)}
                                     if ratios else None,
    }
    (out / "ledger-summary.json").write_text(json.dumps(summary, indent=1, ensure_ascii=False) + "\n")
    (out / "judge-corpus-summary.json").write_text(json.dumps(corpus_summary, indent=1, ensure_ascii=False) + "\n")
    print(json.dumps({"corpus": corpus_summary, "ledger": summary["plans"],
                      "weighted": summary["accepted_counting_duplicates"],
                      "ratios": summary["table_over_packed_seconds"],
                      "packed_only_decls": sorted(decls["packed"] - decls["table"]),
                      "table_only_decls": sorted(decls["table"] - decls["packed"])}, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    main()
