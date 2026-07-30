"""Shared test configuration for the Erdos #12 Python oracle verification suite.

Sets up the Python import path so that oracle modules can be imported
without per-file ``sys.path.insert`` calls.  All test files in this
directory automatically inherit this configuration.

Notes
-----
If the suite is installed as an editable package (``pip install -e .``),
this conftest is not strictly necessary — the imports resolve via
the installed package.  It is retained as a compatibility shim for
users who clone the repository and run ``pytest`` directly.

Copyright (C) 2026 Libertas Technology Group Ltd. All rights reserved.
"""

from __future__ import annotations

import sys
from pathlib import Path


def _ensure_oracle_path() -> None:
    """Add the oracle directory to ``sys.path`` if not already present."""
    oracle_dir = str(Path(__file__).resolve().parent)
    if oracle_dir not in sys.path:
        sys.path.insert(0, oracle_dir)


_ensure_oracle_path()
