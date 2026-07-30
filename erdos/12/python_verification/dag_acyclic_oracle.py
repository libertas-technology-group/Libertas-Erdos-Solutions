#!/usr/bin/env python3
"""
dag_acyclic_oracle.py — Verify the Erdos12 Lean import DAG is acyclic.

Uses Tarjan's SCC algorithm on the import graph of Erdos12 .lean files.

Copyright (C) 2026 Libertas Technology Group Ltd. All rights reserved.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_LEAN_DIR = str(SCRIPT_DIR.parent)  # erdos/12/ (parent of python_verification/)

IMPORT_RE = re.compile(r"^\s*import\s+(.+)$", re.MULTILINE)


def extract_imports(file_path: Path) -> list[str]:
    """Extract import statements from a .lean file.

    Parameters
    ----------
    file_path : Path
        Path to the .lean file.

    Returns
    -------
    list[str]
        List of module names imported.
    """
    if not file_path.is_file():
        return []
    content = file_path.read_text(encoding="utf-8", errors="replace")
    return IMPORT_RE.findall(content)


def tarjan_scc(edges: dict[str, list[str]]) -> list[set[str]]:
    """Tarjan's algorithm for Strongly Connected Components.

    Parameters
    ----------
    edges : dict[str, list[str]]
        Adjacency list: node -> list of neighbours.

    Returns
    -------
    list[set[str]]
        List of SCCs (each is a set of node names).
        SCCs with size > 1 indicate cycles.
    """
    index_counter = [0]
    stack: list[str] = []
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    on_stack: dict[str, bool] = {}
    sccs: list[set[str]] = []

    def strongconnect(node: str) -> None:
        indices[node] = index_counter[0]
        lowlink[node] = index_counter[0]
        index_counter[0] += 1
        stack.append(node)
        on_stack[node] = True

        for neighbour in edges.get(node, []):
            if neighbour not in indices:
                strongconnect(neighbour)
                lowlink[node] = min(lowlink[node], lowlink[neighbour])
            elif neighbour in on_stack and on_stack[neighbour]:
                lowlink[node] = min(lowlink[node], indices[neighbour])

        if lowlink[node] == indices[node]:
            scc: set[str] = set()
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.add(w)
                if w == node:
                    break
            sccs.append(scc)

    for node in edges:
        if node not in indices:
            strongconnect(node)

    return sccs


def resolve_lean_paths(lean_dir: str) -> dict[str, Path]:
    """Find all .lean files and resolve module names.

    Parameters
    ----------
    lean_dir : str
        Directory containing .lean files.

    Returns
    -------
    dict[str, Path]
        Module name -> file path mapping.
    """
    result: dict[str, Path] = {}
    base = Path(lean_dir)
    if not base.is_dir():
        return result
    for f in sorted(base.rglob("*.lean")):
        rel = f.relative_to(base)
        module = str(rel.with_suffix("")).replace("/", ".")
        result[module] = f
    return result


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Verify Erdos12 DAG acyclicity.")
    parser.add_argument(
        "--lean-dir",
        default=None,
        help="Directory with Erdos12 .lean files. "
             "Auto-detects from environment if omitted.",
    )
    args = parser.parse_args()

    # Find the Erdos12 Lean directory
    if args.lean_dir:
        lean_dir = args.lean_dir
    else:
        # Auto-detect relative to this script's location
        candidates = [DEFAULT_LEAN_DIR]
        lean_dir = ""
        for c in candidates:
            if Path(c).is_dir():
                lean_dir = c
                break

    if not lean_dir or not Path(lean_dir).is_dir():
        print("[DAG] ⚠️  Could not find Erdos12 Lean directory. Use --lean-dir.")
        print("[DAG] DAG check SKIPPED (no files to check)")
        sys.exit(3)

    # Build module map
    modules = resolve_lean_paths(lean_dir)
    print(f"[DAG] Found {len(modules)} .lean files in {lean_dir}")

    # Build import graph
    edges: dict[str, list[str]] = {}
    for module, filepath in modules.items():
        imports = extract_imports(filepath)
        edges[module] = imports

    # Run Tarjan SCC
    sccs = tarjan_scc(edges)
    cycles = [scc for scc in sccs if len(scc) > 1]

    print(f"[DAG] {len(modules)} nodes, {sum(len(v) for v in edges.values())} edges")
    print(f"[DAG] {len(cycles)} cycle(s) found")

    if cycles:
        print("[DAG] ❌ FAIL: Cycles detected:")
        for scc in cycles:
            print(f"    - Cycle: {' -> '.join(scc)}")
        sys.exit(1)
    else:
        print("[DAG] ✅ PASS: Import DAG is acyclic")
        sys.exit(0)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, RuntimeError, ImportError, OSError) as e:
        print(f"[DAG] FATAL: {e}", file=sys.stderr)
        sys.exit(2)
