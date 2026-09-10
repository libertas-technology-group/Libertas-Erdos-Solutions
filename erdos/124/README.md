# Erdős Problem 124 — carry-family proofs

*Reference:* [erdosproblems.com/124](https://www.erdosproblems.com/124)

These proofs were **generated** by the Libertas Knowledge Generator (the
deterministic pure-math Lean environment in Libertas-AI-Superintelligence) and
**kernel-verified** — the Lean kernel is the only judge.  They were deposited
by the W4 batch run of 2026-08-25 and promoted verbatim into this frozen bank
(the same file that passed the kernel is the file here).

Each file is self-contained: it defines the `carryValue`/`anchor` vocabulary
for its tuple and proves `carryValue_unbounded_<tuple>`, the statement that the
carry-family bound holds for all `j ≥ e` under the anchor + base + flip
hypotheses.

## The sample

| Lemma | Set | Size | Anchor | Notes |
|-------|-----|------|--------|-------|
| `carryValue_unbounded_T3_4_7` | {3,4,7} | 3 | 582 | seed family {3,4,...}, anchor 582 |
| `carryValue_unbounded_T3_4_8_43` | {3,4,8,43} | 4 | — | |
| `carryValue_unbounded_T3_4_9_25` | {3,4,9,25} | 4 | 659 | anchor 659 |
| `carryValue_unbounded_T3_4_10_19` | {3,4,10,19} | 4 | — | retry path (2 attempts) |
| `carryValue_unbounded_T3_4_12_23_34` | {3,4,12,23,34} | 5 | — | |
| `carryValue_unbounded_T3_4_10_31_46` | {3,4,10,31,46} | 5 | — | |
| `carryValue_unbounded_T3_4_13_17_49` | {3,4,13,17,49} | 5 | — | |
| `carryValue_unbounded_T3_4_21_22_29_31` | {3,4,21,22,29,31} | 6 | — | widest-spread size-6 sample |
| `carryValue_unbounded_T3_4_17_22_29_49` | {3,4,17,22,29,49} | 6 | — | retry path: attempt_01 FAIL → attempt_02 PASS |
| `carryValue_unbounded_T3_4_13_31_37_46` | {3,4,13,31,37,46} | 6 | — | size 6 |
| `carryValue_unbounded_T3_5_6_37_46` | {3,5,6,37,46} | 5 | — | seed family {3,5,...} |
| `carryValue_unbounded_T3_5_7_31_37_46` | {3,5,7,31,37,46} | 6 | — | seed family {3,5,...}, size 6 |

This is a **representative sample** of the W4 batch — spanning set sizes 3/4/5/6,
both seed families, both special anchors, and the FAIL→PASS retry path — pinned
as the frozen proof bank.  The kernel PASSed these tuples on 2026-08-25;
`PROVENANCE_<tuple>.yaml` records the Lean toolchain, the Palomar floor status,
the statement signature, and the generating model.

## Provenance

Each `PROVENANCE_<tuple>.yaml` records:
- `lean_toolchain` — the exact `lake env lean` stamp used by the kernel judge
- `palomar_recommended_min` / `palomar_floor_met` — Palomar registry floor check
- `statement_sig` — `sha256:` of the generated statement (anti-drift)
- `model` — the generating open-weight model
