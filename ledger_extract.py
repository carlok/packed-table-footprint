#!/usr/bin/env python3
"""Collect the finOpTable false certificates from the solver repository of Ma, Zhang
and Cázares
(the-omega-institute/sair-eqt2-stage2-solver) and reduce them to distinct ones.

The certificates are treated as data. Each one is rebuilt from its parsed table by
the template below and compared byte for byte with the original, so the text handed
to Lean is known in advance. Equation text comes from the ETP's eq_size5 file, where
line k is law k.

    ledger_extract.py CLONE/results EQ_SIZE5.gz OUT_SPECS.json OUT_STATS.json
"""
import collections
import gzip
import hashlib
import json
import os
import re
import sys
from pathlib import Path

TABLE = re.compile(r'finOpTable "(\[\[.*?\]\])"')
TEMPLATE = ("import JudgeProblem\nimport JudgeDecide.DecideBang\nimport JudgeFinOp.MemoFinOp\nopen MemoFinOp\n\n"
            "set_option maxRecDepth 1000000 in\nset_option maxHeartbeats 1000000 in\n"
            "def submission : Goal := by\n  let m : Magma (Fin {n}) := {{\n    op := finOpTable \"{t}\"\n  }}\n"
            "  refine ⟨Fin {n}, m, ?_⟩\n  decideFin!\n")


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
    total = other = mismatched = 0
    weight = collections.Counter()
    tables = {}
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
                if r.get("verdict") != "false" or not isinstance(r.get("code"), str):
                    continue
                seen = True
                m = TABLE.search(r["code"])
                if not m:
                    other += 1
                    continue
                total += 1
                t = m.group(1)
                n = len(json.loads(t))
                assert all(len(row) == n and all(0 <= v < n for v in row) for row in json.loads(t))
                if TEMPLATE.format(n=n, t=t) != r["code"]:
                    mismatched += 1
                key = (r["eq1_id"], r["eq2_id"], t)
                weight[key] += 1
                tables[key] = n
            files += seen
    specs = []
    for (a, b, t), w in sorted(weight.items()):
        n = tables[(a, b, t)]
        specs.append({"id": f"ledger_{a}_{b}_{hashlib.sha256(t.encode()).hexdigest()[:8]}",
                      "eq1_id": a, "eq2_id": b, "equation1": eq[a - 1], "equation2": eq[b - 1],
                      "code": TEMPLATE.format(n=n, t=t), "weight": w})
    assert len({s["id"] for s in specs}) == len(specs)
    Path(out_specs).write_text(json.dumps(specs, ensure_ascii=False) + "\n", encoding="utf-8")
    stats = {"files": files, "finOpTable_certificates": total, "other_false_certificates": other,
             "differ_from_template": mismatched, "distinct_certificates": len(specs),
             "distinct_tables": len({k[2] for k in weight}), "distinct_law_pairs": len({k[:2] for k in weight}),
             "distinct_by_carrier": dict(sorted(collections.Counter(tables.values()).items()))}
    Path(out_stats).write_text(json.dumps(stats, indent=1) + "\n")
    print(json.dumps(stats))


if __name__ == "__main__":
    main()
