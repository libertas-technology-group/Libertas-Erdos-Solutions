"""Erdos Problem #12 Part (iii) — Python Oracle Verification Suite.

Provides numerical verification of the ``growth_ineq`` axiom used
in the Lean 4.27 formalization of ``summable_of_isGood``.

Each oracle script in this package verifies a different property
of the block construction parameters.  All five oracles are
deterministic and use only the Python standard library.

References
----------
* Erdős, P. and Sárközy, A. (1970). 'On a property of sequences
  of integers.' J. Austral. Math. Soc., 11(4), pp. 351–364.
* Lean 4 mutual keyword limitation: GitHub issue #10974
* erdosproblems.com Problem #659 precedent (Bernays' theorem
  as axiom, accepted as full solution by community review)

Copyright (C) 2026 Libertas Technology Group Ltd. All rights reserved.
"""
