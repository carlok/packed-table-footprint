# The infinite-only list, pair by pair

`data/etp/infinite-only.tsv` in parsimagma holds 820 pairs: 610 `unresolved` and 210 `saturation_refuted`. The main README's section "The infinite-only list" gives the totals. This folder has the detail.

| File | What it is |
| --- | --- |
| `infinite-map.tsv` | One row per pair: `set`, `how` (direct, closure or dual), `best_class`, `best_model`, the ETP `file`, `line` and `theorem`, `all_classes`, and `zero_axiom_judge`, the models accepted at zero (`-` if none). |
| `facts.tsv` | One row per ETP fact used: 130 facts in 39 files, with the pairs each covers. |
| `certificates.json` | 470 certificates, 173 distinct as text: `id`, the laws, `model`, `set` and `code`. They cover the 387 of the 610 and the 45 of the 210. |
| `judge-rows.jsonl` | Each judge call: policy, status, axioms, direct declarations, seconds, bytes, `code_sha`. No certificate text. |
| `summary.json`, `map-summary.txt` | Counts by model and by class. |
| `examples/` | Four of the translation-invariant certificates as `.lean` files. |

`best_class`: E explicit finite case analysis, W explicit on words, C confluent normal forms (`ConfMagma`), and Ga, Gg, Gs, Gt, Gv the greedy families. A pair can have more than one route; `all_classes` lists them.

**How the certificates ran.** `verify_answer` at `817a465`, Lean 4.33.1, `DEFAULT_PROOF_POLICY` with `allowed_axioms: []`. 472 calls at zero, 471 accepted with an empty closure. The one rejection is your `hard2_0027` as recorded in the ledger, run as a baseline. That certificate and `hard2_0051`'s are not in `certificates.json`, so it holds 470. Re-checks through the judge covered 39 of the certificates, and the attribution of all 820 pairs was recounted.

**What the 12 models are not.** They are translation-invariant models on Z for pairs the ETP reaches only greedily. Translation invariance is an ETP technique, and these particular models were not found in the ETP or in the public Zulip archive by keyword search. Nothing here says they are new.

**What this does not show.** No negative result is claimed for the 223 of the 610 still open, or for the 165 of the 210.
