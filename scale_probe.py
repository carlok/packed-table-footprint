#!/usr/bin/env python3
"""Packed certificates above the published carriers: three models of Theorem F in
magma-1518-obstruction-lean (law 1518, not 3862), sizes 15, 39 and 75, over Z/m with
i -> r for (m, r) = (5, 2), (13, 5), (25, 7). Tables in results/scale-models.json.

Measures whether the literal elaborates under plain `decide`, and at what cost. There
is no finOpTable pair here: its parser reads single digits, so n <= 10.

    scale_probe.py WORKDIR OUT_JSON
"""
import json
import os
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.33.1/bin/lean"


def check(table):
    n = len(table)
    assert all(x == table[table[y][y]][table[x][table[y][x]]] for x in range(n) for y in range(n))
    assert not all(table[x][x] == table[table[x][table[x][x]]][x] for x in range(n))


def certificate(table, prefix, tactic="decide"):
    n = len(table)
    tbl = sum(table[i][j] * n ** (n * i + j) for i in range(n) for j in range(n))
    return (
        f"def tbl : Nat := {tbl}\n"
        f"def op (x y : Fin {n}) : Fin {n} := ⟨(tbl / {n} ^ (x.val * {n} + y.val)) % {n}, Nat.mod_lt _ (by decide)⟩\n\n"
        f"set_option maxRecDepth 1000000 in\n{prefix}"
        "theorem certificate : ∃ (G : Type) (f : G → G → G),\n"
        "    (∀ x y : G, x = f (f y y) (f x (f y x))) ∧ ¬ (∀ x : G, f x x = f (f x (f x x)) x) :=\n"
        f"  ⟨Fin {n}, op, by {tactic}⟩\n\n"
        "#print axioms certificate\n"
    )


def main():
    sys.set_int_max_str_digits(0)  # the n = 75 literal has more than 4300 digits
    work = Path(sys.argv[1]).resolve()
    work.mkdir(parents=True, exist_ok=True)
    models = json.loads((HERE / "results/scale-models.json").read_text())
    out = []
    runs = [("decide", "", "decide"),
            ("threshold", "set_option exponentiation.threshold 100000 in\n", "decide"),
            ("kernel", "", "decide +kernel")]
    for name, table in models.items():
        check(table)
        for mode, prefix, tactic in runs:
            code = certificate(table, prefix, tactic)
            path = work / f"{name}_{mode}.lean"
            path.write_text(code, encoding="utf-8")
            start = time.monotonic()
            try:
                proc = subprocess.run([str(LEAN), str(path)], text=True, capture_output=True, timeout=300,
                                      env=dict(os.environ))
                text = proc.stdout + proc.stderr
                code_rc = proc.returncode
            except subprocess.TimeoutExpired:
                text, code_rc = "TIMEOUT", -1
            row = {"model": name, "n": len(table), "mode": mode, "rc": code_rc,
                   "seconds": round(time.monotonic() - start, 1), "bytes": len(code.encode()),
                   "axioms": next((l for l in text.splitlines() if "axioms" in l), None),
                   "error": text[:300] if code_rc else None}
            out.append(row)
            print(row["model"], row["mode"], "rc", row["rc"], row["seconds"], "s", row["bytes"], "bytes",
                  row["axioms"], (row["error"] or "")[:200].replace("\n", " "), flush=True)
    Path(sys.argv[2]).write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
