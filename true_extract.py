#!/usr/bin/env python3
"""Collect verdict=true certificates from the results/ tree of the solver by Ma, Zhang
and Cázares, the way
ledger_extract.py collects the false ones, and deduplicate them.

Certificates are data here: nothing is compiled or executed by this script.

    true_extract.py CLONE/results EQ_SIZE5.gz OUT_SPECS.json OUT_STATS.json

Output specs: one per distinct (eq1, eq2, code), with weight (how many ledger rows),
and code_group (id of the exact code text, so distinct-by-code can be counted).
"""
import collections
import gzip
import hashlib
import json
import os
import re
import sys
from pathlib import Path


def rows(obj):
    if isinstance(obj, dict):
        if "verdict" in obj and "code" in obj and "eq1_id" in obj:
            yield obj
        else:
            for v in obj.values():
                yield from rows(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from rows(v)


def main():
    results, size5, out_specs, out_stats = sys.argv[1:5]
    eq = gzip.open(size5, "rt", encoding="utf-8").read().splitlines()
    files = 0
    total = 0
    nocode = 0
    weight = collections.Counter()
    weight_code = collections.Counter()
    file_of = collections.defaultdict(set)
    bad_eq = 0
    for dp, _, fn in os.walk(results):
        for f in sorted(fn):
            if not f.endswith(".json"):
                continue
            try:
                data = json.load(open(os.path.join(dp, f), encoding="utf-8"))
            except ValueError:
                continue
            seen = False
            for r in rows(data):
                if r.get("verdict") != "true":
                    continue
                if not isinstance(r.get("code"), str):
                    nocode += 1
                    continue
                seen = True
                total += 1
                key = (r["eq1_id"], r["eq2_id"], r["code"])
                weight[key] += 1
                weight_code[r["code"]] += 1
                file_of[key].add(os.path.relpath(os.path.join(dp, f), results))
            files += seen
    specs = []
    for (a, b, c), w in sorted(weight.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][2])):
        if not (1 <= a <= len(eq) and 1 <= b <= len(eq)):
            bad_eq += 1
            continue
        h = hashlib.sha256(c.encode("utf-8")).hexdigest()
        specs.append({"id": f"true_{a}_{b}_{h[:10]}", "eq1_id": a, "eq2_id": b, "equation1": eq[a - 1],
                      "equation2": eq[b - 1], "code": c, "weight": w, "code_sha": h[:16],
                      "code_weight": weight_code[c], "n_files": len(file_of[(a, b, c)])})
    assert len({s["id"] for s in specs}) == len(specs)
    Path(out_specs).write_text(json.dumps(specs, ensure_ascii=False) + "\n", encoding="utf-8")
    stats = {"files_with_true_code": files, "true_rows_with_code": total, "true_rows_without_code": nocode,
             "distinct_code": len(weight_code), "distinct_problem_code": len(weight),
             "distinct_problems": len({(a, b) for a, b, _ in weight}), "eq_out_of_range": bad_eq}
    Path(out_stats).write_text(json.dumps(stats, indent=1) + "\n")
    print(json.dumps(stats))


if __name__ == "__main__":
    main()
