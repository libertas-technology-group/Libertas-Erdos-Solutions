"""Smoke tests for the Erdos #12 Part (iii) Python oracle verification suite.

Each test runs an oracle's verification function with its default
parameters and asserts a passing result.  These are integration tests —
they confirm that the oracles execute without error and report the
expected outcome.  They do not re-prove the mathematics (the oracles
already perform that verification).

All oracle modules are imported at module level via a ``conftest.py``
that configures the import path once, avoiding per-file ``sys.path``
hacks.

Copyright (C) 2026 Libertas Technology Group Ltd. All rights reserved.
"""

from __future__ import annotations

import pytest

import block_structure_oracle

# ── Oracle module-level imports ────────────────────────────────────────────
# The conftest.py in this directory handles path configuration.
import coprimality_oracle
import d23_axiom_oracle
import dag_acyclic_oracle
import sum_bound_oracle
from block_structure_oracle import (
    verify_bounds,
    verify_mod_F_eq_0,
    verify_mod_F_eq_1,
    verify_P_increasing,
)
from coprimality_oracle import (
    verify_F_bound,
    verify_FM_coprime,
    verify_ge_3,
    verify_pairwise_coprime,
)
from d23_axiom_oracle import (
    check_block_elements_mod_F_eq_1,
    check_growth_ineq,
    check_primitives_stable,
)
from dag_acyclic_oracle import tarjan_scc
from sum_bound_oracle import verify_ratio_bounds, verify_summability

# ═══════════════════════════════════════════════════════════════════════════
# Coprimality oracle
# ═══════════════════════════════════════════════════════════════════════════

class TestCoprimalityOracle:
    """Verify the coprime sequence properties used in the CRT construction."""

    def test_module_imports(self) -> None:
        """``coprimality_oracle`` imports without error."""
        assert coprimality_oracle is not None

    def test_verify_F_lower_bound(self) -> None:
        """``verify_ge_3`` returns ``(True, ...)`` for default max_i."""
        ok, _failures = verify_ge_3(max_i=10)
        assert ok is True

    def test_verify_pairwise_coprime(self) -> None:
        """``verify_pairwise_coprime`` returns ``(True, ...)`` for default max_i."""
        ok, _failures = verify_pairwise_coprime(max_i=10)
        assert ok is True

    def test_verify_exponential_bound(self) -> None:
        """``verify_F_bound`` returns ``(True, ...)`` for default max_i."""
        ok, _failures = verify_F_bound(max_i=10)
        assert ok is True

    def test_verify_gcd_with_M(self) -> None:
        """``verify_FM_coprime`` returns ``(True, ...)`` for default max_i."""
        ok, _failures = verify_FM_coprime(max_i=10)
        assert ok is True


# ═══════════════════════════════════════════════════════════════════════════
# Sum bound oracle
# ═══════════════════════════════════════════════════════════════════════════

class TestSumBoundOracle:
    """Verify the summability of X(i)/P(i) needed for the convergence argument."""

    def test_module_imports(self) -> None:
        """``sum_bound_oracle`` imports without error."""
        assert sum_bound_oracle is not None

    def test_verify_ratio_bounds(self) -> None:
        """``verify_ratio_bounds`` returns an empty failure list for default max_i."""
        failures = verify_ratio_bounds(max_i=8)
        assert isinstance(failures, list)
        assert len(failures) == 0

    def test_verify_summability(self) -> None:
        """``verify_summability`` returns an empty failure list for default max_i."""
        failures = verify_summability(max_i=8)
        assert isinstance(failures, list)
        assert len(failures) == 0


# ═══════════════════════════════════════════════════════════════════════════
# Block structure oracle
# ═══════════════════════════════════════════════════════════════════════════

class TestBlockStructureOracle:
    """Verify the block decomposition invariants used in Theorem 3.1."""

    def test_module_imports(self) -> None:
        """``block_structure_oracle`` imports without error."""
        assert block_structure_oracle is not None

    def test_verify_mod_F_eq_0(self) -> None:
        """``verify_mod_F_eq_0`` returns ``(True, ...)`` for default max_i."""
        ok, _failures = verify_mod_F_eq_0(max_i=5)
        assert ok is True

    def test_verify_mod_F_eq_1(self) -> None:
        """``verify_mod_F_eq_1`` returns ``(True, ...)`` for default max_i."""
        ok, _failures = verify_mod_F_eq_1(max_i=5)
        assert ok is True

    def test_verify_bounds(self) -> None:
        """``verify_bounds`` returns ``(True, ...)`` for default max_i."""
        ok, _failures = verify_bounds(max_i=5)
        assert ok is True

    def test_verify_P_increasing(self) -> None:
        """``verify_P_increasing`` returns ``(True, ...)`` for default max_i."""
        ok, _failures = verify_P_increasing(max_i=5)
        assert ok is True


# ═══════════════════════════════════════════════════════════════════════════
# D23 axiom oracle
# ═══════════════════════════════════════════════════════════════════════════

class TestD23AxiomOracle:
    """Verify the growth_ineq axiom consistency and related D23 checks."""

    def test_module_imports(self) -> None:
        """``d23_axiom_oracle`` imports without error."""
        assert d23_axiom_oracle is not None

    def test_check_growth_ineq(self) -> None:
        """``check_growth_ineq`` returns ``(True, ...)`` for default max_i."""
        ok, _msg = check_growth_ineq(max_i=5)
        assert ok is True

    def test_check_primitives_stable(self) -> None:
        """``check_primitives_stable`` returns ``True`` for default max_i."""
        assert check_primitives_stable(max_i=5) is True

    def test_check_block_elements_mod_F_eq_1(self) -> None:
        """``check_block_elements_mod_F_eq_1`` re-verifies cross-block modularity."""
        assert check_block_elements_mod_F_eq_1(max_i=5) is True


# ═══════════════════════════════════════════════════════════════════════════
# DAG acyclic oracle
# ═══════════════════════════════════════════════════════════════════════════

class TestDAGAcyclicOracle:
    """Verify the Tarjan SCC implementation on known graph topologies."""

    def test_module_imports(self) -> None:
        """``dag_acyclic_oracle`` imports without error."""
        assert dag_acyclic_oracle is not None

    def test_tarjan_scc_empty_graph(self) -> None:
        """Tarjan SCC on an empty graph returns zero components."""
        sccs = tarjan_scc({})
        assert len(sccs) == 0

    def test_tarjan_scc_single_node(self) -> None:
        """Tarjan SCC on a single-node graph returns one component."""
        sccs = tarjan_scc({"a": []})
        assert len(sccs) == 1

    def test_tarjan_scc_dag(self) -> None:
        """Tarjan SCC on an acyclic graph assigns each node its own component."""
        edges = {"a": ["b"], "b": ["c"], "c": []}
        sccs = tarjan_scc(edges)
        assert len(sccs) == 3

    def test_tarjan_scc_cycle(self) -> None:
        """Tarjan SCC on a 3-cycle collapses all nodes into one component."""
        edges = {"a": ["b"], "b": ["c"], "c": ["a"]}
        sccs = tarjan_scc(edges)
        assert len(sccs) == 1
