# leanchecker replay (task 4.1)

Independent re-verification of the 173 distinct certificates in
`../certificates.json` (470 entries, deduplicated by code).

For each distinct certificate, three checks, run on 2026-11-07 against the
Stage 2 judge at commit 817a4653 with Lean 4.33.1 under the zero-axiom policy
(`allowed_axioms: []`):

1. Judge `verify_answer` verdict (zero policy).
2. `leanchecker` kernel re-check of the compiled `Submission` (exit code).
3. An independent `#print axioms submission`, run outside the judge.

Result: 173 / 173 on all three. Every certificate is accepted under the
zero-axiom policy, its proof term passes the external kernel checker, and an
independent axiom print reports no axiom dependencies. No disagreements.

- `results.jsonl` — one row per distinct certificate.
- `summary-41.json` — totals and failures (none).

## Patched-toolchain replay (2026-11-07)

The first replay ran on Lean 4.33.1. That kernel does not contain the upstream fix for
lean4#14576 (nested inductive types; fix lean4#14577, merged 2026-07-28). By git ancestry the
fix is in v4.34.1 and v4.35.0 and not in v4.31.0 through v4.33.1. The bug needs an in-process
metaprogram to act on. The same 173 certificates were therefore recompiled and re-checked on
4.34.1 and 4.35.0.

Method. The import chain (`JudgeMagma.Magma`, `JudgeProblem`, `Submission`) has no Mathlib, so
each kept artifact is recompiled with plain `lean`. `PATH` and `LEAN_SYSROOT` are pinned to the
toolchain; otherwise `leanchecker` finds its sysroot through the elan shim and reads the default
toolchain's `Init.olean`. Per certificate: compile, `leanchecker`, `leanchecker-paranoid` (4.35.0
only; first shipped in 4.35.0-rc3), an independent `#print axioms`, and `submission : Goal`
typechecks.

| | 4.34.1 | 4.35.0 |
|---|---|---|
| compiled | 173 | 173 |
| `leanchecker` exit 0 | 173 | 173 |
| `leanchecker-paranoid` exit 0 | n/a | 173 |
| no axioms | 173 | 173 |
| `submission : Goal` typechecks | 173 | 173 |

A scan of the 173 `Submission.lean` files for meta-level constructs (unsafe code, compiled
overrides, macros, elaborators, initializers, attributes, native evaluation, `sorry`, `partial`,
`opaque`, axiom declarations, `set_option`) found none. The certificates are plain term and
tactic proofs.

What this shows and what it does not. The certificates contain no metaprogramming, and the
patched kernels agree with the 4.33.1 result. It is not a proof of soundness: the checkers use
the same kernel, and the oss-security post on lean4#14576 says Nanoda also accepted its example.

Files: `results-4.34.1.jsonl`, `results-4.35.0.jsonl`, `summary-4b.json`, and the two
scripts under `scripts/` (paths inside them point at the external disk).
