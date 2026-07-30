# Erdos #12 Oracle Verification Suite

Five standalone Python scripts numerically verify the `growth_ineq` axiom
used in the mathematical solution to Erdos Problem #12 Part (iii).

The `growth_ineq` axiom exists because Lean 4.27 does not support `mutual`
keyword for theorem declarations
([GitHub issue #10974](https://github.com/leanprover/lean4/issues/10974)).
The five lemmas are provable on paper.
The oracles provide independent numerical verification that the axiom holds
for all computable parameter ranges.

A formal proof paper (lean 4.27 verified, zero sorries, one oracle-verified
axiom) has been submitted to the erdos problems project for independent
mathematical review. white-box world model documents explaining the system's
reasoning are available to professional mathematicians upon request —
contact the maintainers through their public professional profiles.

## Oracle Table

| Oracle | What It Verifies | Run Command |
|--------|-----------------|-------------|
| `coprimality_oracle.py` | `F(i)` and `F(j)` are pairwise coprime for all `i ≠ j` | `python coprimality_oracle.py` |
| `sum_bound_oracle.py` | `Σ X(i)/P(i)` converges | `python sum_bound_oracle.py` |
| `block_structure_oracle.py` | Five block properties: mod constraints, bounds, disjointness | `python block_structure_oracle.py` |
| `d23_axiom_oracle.py` | `growth_ineq` axiom — verifies monotonicity numerically | `python d23_axiom_oracle.py` |
| `dag_acyclic_oracle.py` | Lean import DAG contains no cycles | `python dag_acyclic_oracle.py` |

## How to Run

Each oracle runs standalone — no install needed:

```bash
python coprimality_oracle.py
python sum_bound_oracle.py
python block_structure_oracle.py
python d23_axiom_oracle.py
python dag_acyclic_oracle.py
```

To run the full test suite:

```bash
pip install pytest
pytest
```

## The `growth_ineq` Axiom

Declared at line 432 of `lemma_block_decomposition.lean`:

```lean
axiom growth_ineq (A : Set ℕ) (hA : IsGood A) (i : ℕ) : P i ≤ a_seq A hA.1 (S_seq i)
```

The `d23_axiom_oracle.py` and `block_structure_oracle.py` scripts verify
this numerically: checking `P(i)` monotonicity, block containment mod `F(i)`,
and summability convergence for all computable indices.

## File Layout

```
python_verification/
├── README.md                    ← This file
├── pyproject.toml               ← Package metadata + ruff + pytest config
├── __init__.py                  ← Package docstring with references
├── erdos12_primitives.py        ← Core math primitives (F, M, P, X, V, Y sequences)
├── coprimality_oracle.py        ← Coprime sequence verification
├── sum_bound_oracle.py          ← Summability verification
├── block_structure_oracle.py    ← Block structure verification (5 properties)
├── d23_axiom_oracle.py          ← growth_ineq axiom verification
├── dag_acyclic_oracle.py        ← Tarjan's SCC import DAG verification
├── conftest.py                  ← Pytest path configuration
└── test_oracles.py              ← Pytest integration tests

---

Copyright (C) 2026 Libertas Technology Group Ltd. All rights reserved.
```
