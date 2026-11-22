# Paired axiom-footprint test for the packed table encoding

The question: does a countermodel's table, read out of one natural-number literal with `tbl / n ^ (x * n + y) % n`, close over fewer axioms than `finOpTable`?

Yes. Run through the competition's own judge, the packed form closes over nothing on all 100 countermodels published in parsimagma and on all 4,240 `finOpTable` certificates in the ledger of the solver by Ma, Zhang and Cázares.

Sources and what was changed are in `NOTICE`.

## Result

Same goal, same tactic (`decideFin!`), same options, only the operation rewritten and the `MemoFinOp` import it no longer needs dropped (keeping it changes nothing on a sample of 12). `verify_answer` at commit `817a465` of `SAIRcompetition/equational-theories-lean-stage2`, Lean 4.33.1. "Official" is the runner's `DEFAULT_PROOF_POLICY`; "zero-axiom" is the same policy with no axioms allowed.

**The 100 countermodels in `dist/solo/certificates/`**, 800 judge calls:

| Operation written as | Closes over | Official | Zero-axiom | Largest certificate |
| --- | --- | ---: | ---: | ---: |
| `finOpTable` on a string (as published) | `propext`, `Quot.sound`, `Classical.choice` | 100 | 0 | 371 B |
| List literal, `List.getD` | `propext` | 100 | 0 | 477 B |
| List literal, lookup with no catch-all | nothing | 100 | 100 | 572 B |
| Packed `Nat` literal | nothing | 100 | 100 | 391 B |

Row-level results are in `results/judge-corpus.json`, and the packed certificates in `results/packed-certificates.json`.

**The ledger.** The JSON files under `results/` of `the-omega-institute/sair-eqt2-stage2-solver` at commit `4bf87e3` hold together, counting result rows with problem ids, exactly 4,240 `finOpTable` false certificates. All are byte-identical to one template. They reduce to 1,494 law pair and table combinations, which are 172 distinct as text (156 tables up to isomorphism), carriers 2 to 9. Each combination ran once in each encoding, 2,988 judge calls:

| Encoding, policy | Accepted | Counting duplicates | Closes over |
| --- | ---: | ---: | --- |
| `finOpTable`, official | 1,494 / 1,494 | 4,240 | `propext`, `Quot.sound`, `Classical.choice` |
| Packed, zero-axiom | 1,494 / 1,494 | 4,240 | nothing |

## Time and size

Median judge time per call in seconds. "Alone" is one worker at a time on AC power, on 4 certificates per carrier, two rounds, load at most 3.77 (`results/speed-alone-c1.jsonl`). "8 workers" is the full ledger run, also on AC.

| Carrier | Certificates | Packed, alone | `finOpTable`, alone | Packed, 8 workers, median / max | `finOpTable`, 8 workers, median / max |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 702 | 1.73 | 1.75 | 3.13 / 13.49 | 3.18 / 13.63 |
| 3 | 365 | 1.69 | 1.79 | 3.10 / 13.24 | 3.32 / 14.36 |
| 4 | 61 | 1.70 | 1.97 | 2.90 / 11.79 | 3.41 / 16.19 |
| 5 | 82 | 1.70 | 2.28 | 3.00 / 11.14 | 4.15 / 18.63 |
| 6 | 13 | 1.69 | 2.98 | 3.09 / 3.27 | 5.63 / 5.85 |
| 7 | 11 | 1.70 | 4.02 | 3.03 / 3.59 | 7.34 / 7.68 |
| 8 | 23 | 1.83 | 5.82 | 3.23 / 11.62 | 10.52 / 43.58 |
| 9 | 237 | 1.80 | 7.64 | 3.22 / 13.59 | 14.19 / 72.24 |

- The 8-worker medians are 1.7 to 1.9 times the alone figures in both encodings, and the ratio at carrier 9 is 4.2 alone and 4.4 at 8 workers.
- The maxima are not properties of the certificates. The 72.24 s call came in one of two slow spells of that run, when even packed at carrier 2 took about 10 s, and the same certificate takes 7.7 s wall and 7.9 s CPU alone, 1.8 s packed. The spells' cause is unrecorded, so "load" is an inference.
- Packed grows with instances: at 6,561 it takes 3.1 s alone against 9.6 s.
- A List literal is within about 0.4 s of packed at carrier 8 and at 729 instances at carrier 9, and 0.6 to 1.0 s above it at 6,561 instances (`results/speed-alone-c5.jsonl`). `finOpTable` costs about 4 s more at carrier 8 and about 6 s more at carrier 9. So the gap is the string being decoded, which under plain `decide` happens in the elaborator and again in the kernel, with 40 to 44 percent of that time in the elaborator.
- Upstream has changed the kernel reduction of `String.toList` (lean4#16012, PR #16113, merged 30 October 2026). No release has it, and no toolchain with it was measured.
- Totals at 8 workers: 5,298 s packed, 8,784 s `finOpTable`. Aggregates are in `results/ledger-summary.json`.
- Size: 404 B median and 480 B largest packed, 323 B and 551 B `finOpTable`, under a cap of 20,000. Packed is the larger on 1,223 of the 1,494.

**Above carrier 9.** The ledger stops at 9. At carrier 10 a pair still exists, checked on one trivial pair: the three against nothing. Above that `finOpTable`'s single-digit parser no longer reads the table faithfully, so there is no pair. Three models of Theorem F from `magma-1518-obstruction-lean` (law 1518, not 3862) certify under `decide` with nothing in the closure and the default exponentiation threshold, with `maxRecDepth` raised and in plain Lean (`results/scale.json`). Lean warns at 39 and 75 that the exponent passes that threshold, and the check still completes. They also pass the judge at the zero-axiom policy.

| n | Bytes, plain Lean | Seconds, `decide` | Seconds, judge, at load 60 to 94 |
| ---: | ---: | ---: | ---: |
| 15 | 633 | 0.3 | 4.5 |
| 39 | 2,788 | 0.9 | 6.3 |
| 75 | 10,915 | 3 to 18, depending on load | 16.8 |

## Where the axioms enter

Shortest chains on 4.33.1, abridged, by a breadth-first walk over the constants each declaration uses (`AxiomPaths.lean`, output in `results/axiom-chains-4.33.1.txt`).

- All three come from `String.toList`, which decodes UTF-8:
  - `propext`: `String.toList` → `String.Internal.toArray` → `ByteArray.isSome_utf8Decode?_iff`
  - `Classical.choice`: … → `ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract` → `Classical.propDecidable`
  - `Quot.sound`: … → `ByteArray.utf8Decode?.go` → `ByteArray.le_size_of_utf8DecodeChar?_eq_some` → `funext`
- `List.getD` adds `propext` on its own, as `docs/SUBSTRATE_NOTES.md` in the solver repository already records. The route, which it does not give: `List.get?Internal._sparseCasesOn_1` → `Nat.land` → `Nat.bitwise`, whose termination proof reaches `Nat.div_lt_self`. The route has nothing specific to lists: any catch-all match over an inductive's constructors (`List`, `Option`, `Bool`, an enum, a user inductive) brings `propext` the same way, and spelling out every constructor is clean. So the table's "lookup with no catch-all" row depends on that shape, which `judge_run.py`'s `nth` has.
- `List.filterMap`, `Char.isDigit`, `Char.toNat`, `Nat.mod_lt`, `Nat.decidableForallFin` and `instDecidableEqFin` close over nothing. So does the string as data, read through `toUTF8`.

`memofinop-three-lines.diff` shows this directly on a patched copy of the judge, not the official one. With `s.toUTF8.data.toList` and `(l.drop i).headD` in `MemoFinOp.lean`, 104 distinct `finOpTable` certificates pass byte-unchanged at zero axioms with an empty closure, and 8 mutated tables are rejected. `PatchedParserEqual.lean` proves the patched parser equals the original on every string. That proof closes over the three, since it is about the original; it is a check, not part of any certificate.

The footprints above are the same on 4.32.2, 4.33.1, 4.34.1 and 4.35.0, on all four encodings of the carrier-6 model.

## The rest of the ledger

The ledger's false side has 12 other rows, six texts (labelled below by SHA-256 prefix), on two problems.

- `hard2_0051`, 4 rows: arithmetic already, and passes at zero as written (`f7307c673051`, 375 B).
- `hard2_0027`, 8 rows, 5 texts: 2 rows are the current emission `dd26586983db`, which closes over `propext` and `Quot.sound`; 3 are an older form importing Mathlib; 3 are retry drafts that do not compile on `817a465`.

Packing cannot reach `hard2_0027`. Laws 1167 → 1763 are line 392 of `infinite-only.tsv` in parsimagma, status `unresolved`, and `NoFinite.lean` proves that no finite magma satisfies 1167 and refutes 1763, closing over nothing. `hard2_0027_zero.lean` keeps `def f`, the statement of `f_1659`, `impl` and `f_2473` byte for byte and redoes the proofs from the fuel definitions. It is 8,012 B and accepted at zero with an empty closure. The block is `austin_f_lemmas_hand.txt`, and it is the only change: pasted as `_AUSTIN_F_LEMMAS`, it does the same for all 148 pairs of `infinite-only.tsv` with hypothesis 1659, 2000, 2473 or 1167, at 7,211 to 8,014 B (`results/f148-hand-zero.jsonl`). As emitted, the same 148 are accepted at the official policy with `propext` and `Quot.sound` and rejected at zero. They are 28 distinct certificate texts, and 1 of the 148 is in the ledger.

**True certificates.** The same walk gives 4,126 rows, 1,635 distinct texts, 1,727 distinct by problem and text, on 1,419 problems. All import only `JudgeProblem`, and all 1,727 are accepted at zero with an empty closure (`results/true-half-summary.json`). They use `intro`, `have`, `exact`, `fun`, `congrArg`, `.symm` and `.trans`, with one bare `rfl` and one `first | exact … | grind` fallback that is never taken. `lean432_corpus` already records this for its 88, and all 88 agree.

**Whole ledger.** 2,869 problems have a certificate, on 8,378 rows. 8,372 of those rows are accepted at the official policy without Mathlib; the other 6 are the 3 that need Mathlib and the 3 that do not compile. No pair occurs on both sides. A further 100 problems occur with no certificate anywhere (`research_order5_hard_attempt.json`).

| | Problems passing at zero |
| --- | ---: |
| As recorded (1,419 true plus `hard2_0051`) | 1,420 |
| With the 1,448 `finOpTable` problems packed | 2,868 |
| With `hard2_0027` redone | 2,869 |

This is not a re-emitted ledger. "As recorded" means the rows under `results/`, from several solver generations. On a copy of the solver, replacing the last return of `make_false_code` with `make_false_code_arith(n, None, cex["table"])` and using the new block ran 513 of 513 distinct problems end to end at zero, one judge call each, no LLM. That copy fails `scripts/check_freeze.py` and the assertion at `tests/test_false_side_v2.py:76`, as it should: it is a new solver, not v2.5. Removing the `n > 10` test alone does not work, since the `f2_matrix` witnesses carry no table before that point (13 law pairs, 48 ledger rows). `make_false_code_arith` writes the packed shape already, up to a line break inside `let m`, though no file under `results/` holds one.

## The infinite-only list

`infinite-only.tsv` holds 820 pairs: 610 `unresolved` and 210 `saturation_refuted`. All 820 were attributed to an ETP fact, using closure and duality. Certificates through the judge at the zero-axiom policy: 472 calls, 471 accepted with an empty closure, and the one rejection is the ledger's own `hard2_0027` run as a baseline. The 471 are 174 distinct texts, since the goal comes from `JudgeProblem`.

| What the ETP does | In the 610 | Pass at zero | In the 210 | Pass at zero |
| --- | ---: | ---: | ---: | ---: |
| Has an explicit construction: on N, Z or products, reduced words, `ConfMagma` | 375 | 375 | 191 | 45 |
| Greedy only, five families | 235 | 12 | 19 | 0 |

Seven of the 375 also have a greedy fact in the ETP. The 223 of the 610 still open are all greedy or partly greedy constructions (Terence Tao's summary of 22 November 2024 calls 1323, 1516 and 1729 partly explicit, 9 of the 223), in 20 ETP files: `Equation1076` 76, `Eq511` 24, `Equation1692` 22, `Equation73` 14, `Eq1112` 14, `Equation1722` 10, `Asterix` 8, `Equation917` 8, `Eq707` 7, `Equation713` 6, `Equation1289` 6, `Eq883` 5, `Equation1526` 5, `Equation1729` 4, `Eq118` 3, `Equation1323` 3, `Equation63` 2, `Eq476` 2, `Equation1516` 2, `Eq1648` 2. Of the 210, 165 are open: 146 `ConfMagma` and 19 greedy. The pair-by-pair map and the certificates are in `infinite-map/`.

The 12 closed greedy pairs use translation-invariant models on Z: 1491 =/=> 65, 2061 =/=> 261, 65 =/=> 817, 1491, 3862, 261 =/=> 2644, 2061, 3456, 3308 =/=> 3456, 3511, 4158 =/=> 3862, 3955. Translation invariance is an ETP technique, and on Zulip (10 October 2024) Terence Tao computed, "if I computed correctly", that Daniel Weber's construction on Z × Z obeys 359, 1426, 4065 and 614 and contradicts 3862 and 817. These particular models were not found in the ETP or in the public Zulip archive, whose data runs to 23 October 2026 (by keyword search throughout, reading the Obelix thread and the relevant parts of the law 65 thread in full). That is all that is claimed for them. For example, 1491 =/=> 65: a ◇ b = b + g(b − a), with g(1) = −2, g(−1) = 2, g(d) = −1 for d ≤ −3 and 0 otherwise.

## Limits

- The judge ran with `JUDGE_LEAN_PATH` set to its four `Judge*` modules, built from the same checkout, and without Mathlib, because no certificate measured here imports it; the 3 ledger rows that do ran separately with Mathlib at `0df444a`. The `openai` import in `pipeline/proxy.py` is stubbed to read the policy constant. Nothing else in the judge changed.
- The 100 rows are 25 distinct tables: 9, 12, 2, 1, 1 at carriers 2 to 6. The 27 rows at carrier 4 are two models. The ledger has 172.
- Re-checks ran on samples through the judge: 50 of the 1,727, 30 of the 1,494, 39 of the 472. All 1,727 and all 1,494 also went through a harness with no judge, and 20 packed certificates went through plain `lean` with `#print axioms`. `collectAxioms` has an open false negative (lean4#15226), and an independent walk agrees at carriers 2 to 9.
- The chains are shortest paths, one per axiom, and specific to the toolchain. Other paths may exist. Of the `Nat` theorems in `Init` whose statements mention `/` or `%`, 9 close over nothing: of 292 on 4.32.2 and 4.33.1, 295 on 4.34.1 and 300 on 4.35.0.
- "Alone" means the desktop baseline, load average about 3, not a clean machine.

## Reproduce

Needs `python3` and the Lean 4.33.1 toolchain. Below, `$T` is that toolchain's `bin`, for example `~/.elan/toolchains/leanprover--lean4---v4.33.1/bin`. The inputs `eq_size5.txt.gz`, `infinite-only.tsv` and `sprint12-certificates.json` are on `main` of `github.com/carlok/parsimagma`, in `data/etp/` and `dist/solo/certificates/`. `scale_probe.py` takes the toolchain from exactly that path and needs Python 3.11 or later.

Build the judge's modules from a checkout:

```bash
git clone https://github.com/SAIRcompetition/equational-theories-lean-stage2.git judge && git -C judge checkout 817a465
```

```bash
mkdir -p judge/.lake/build/lib/lean/{JudgeMagma,JudgeDecide,JudgeFinOp,JudgeSupport} && for m in JudgeMagma/Magma JudgeDecide/DecideBang JudgeFinOp/MemoFinOp JudgeSupport/Inspect; do LEAN_PATH=judge/.lake/build/lib/lean $T/lean -R judge/judge -o judge/.lake/build/lib/lean/$m.olean judge/judge/$m.lean; done
```

Run the 100, from a specs file holding the false-verdict rows of `sprint12-certificates.json` with `id`, `eq1_id`, `eq2_id`, `equation1`, `equation2` and `code`:

```bash
LEAN_BIN=$T/lean LAKE_BIN=$T/lake JUDGE_LEAN_PATH=$PWD/judge/.lake/build/lib/lean python3 -I -B judge_run.py --judge judge --input specs.json --out corpus.jsonl --artifacts art --plan table:official,table:zero,list:official,list:zero,nth:official,nth:zero,packed:official,packed:zero
```

Run the ledger, from a clone of the solver repository at `4bf87e3`:

```bash
python3 -I ledger_extract.py sair-eqt2-stage2-solver/results eq_size5.txt.gz ledger-specs.json ledger-stats.json
```

```bash
LEAN_BIN=$T/lean LAKE_BIN=$T/lake JUDGE_LEAN_PATH=$PWD/judge/.lake/build/lib/lean python3 -I -B judge_run.py --judge judge --input ledger-specs.json --out ledger.jsonl --artifacts art --plan packed:zero,table:official
```

Run the true half:

```bash
python3 -I true_extract.py sair-eqt2-stage2-solver/results eq_size5.txt.gz true-specs.json true-stats.json
```

```bash
LEAN_BIN=$T/lean LAKE_BIN=$T/lake JUDGE_LEAN_PATH=$PWD/judge/.lake/build/lib/lean python3 -I -B cert_run.py --judge judge --input true-specs.json --policy zero --verdict true --out true.jsonl --artifacts art-true
```

The rest:

```bash
python3 -I summarize.py corpus.jsonl ledger.jsonl ledger-specs.json ledger-stats.json results
```

```bash
python3 -I -B scale_probe.py scale-work results/scale.json
```

```bash
LEAN_PATH=judge/.lake/build/lib/lean $T/lean AxiomPaths.lean > results/axiom-chains-4.33.1.txt
```

```bash
LEAN_PATH=judge/.lake/build/lib/lean $T/lean PatchedParserEqual.lean
```

```bash
$T/lean NoFinite.lean
```

These commands do not regenerate `results/packed-certificates.json`, `results/speed-alone-*.jsonl`, `results/f148-hand-zero.jsonl` or `results/true-half-summary.json`. `memofinop-three-lines.diff` applies from inside a copy of the clone, with `patch -p0 < ../memofinop-three-lines.diff`.

The judge and solver runs here were inside `sandbox-exec`, with no network and no writes outside the working folder, reading from the home directory only toolchains, this folder and, for the 3 Mathlib rows, the Mathlib packages. That is a precaution when compiling outside material, not a requirement.
