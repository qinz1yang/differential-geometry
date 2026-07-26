# IteratedRmTowerSolution

## Purpose

This file is the trusted solution-facing assembly of the arbitrary-dimensional
curvature-derivative heat tower.  It uses the globally fixed costed residual
field from `SolutionResidual`, rather than the stronger and unsupported
per-summand `IteratedRmTowerOn` witness.

## 2026-07-22 direct tower assembly

`towerHeatSol_raw` works pointwise at an arbitrary regular time of any solution.
It consumes `rmResidual_cost`, whose witness field is selected before the point
and orthonormal basis, and uses the canonical `basisInvMetric` derivative to
assemble `nablaKNormHeatAt` in that same basis.  `StarSum2Cost.bound` and
`nablaKReactionAt_le` give the explicit reaction coefficient
`rmTowerCost (Module.finrank Real E) k`.  `towerHeatSol_any` is now only the
positive-tail restriction wrapper.

The old `exists_rmTowerSol` declaration was removed.  Its per-`j` star-family
conclusion is stronger than the concrete fixed residual factorization and its
proof was a `sorry`; it is not retained as a compatibility theorem or trusted
intermediate.

Source assembly is complete and contains no `sorry`, `admit`, or new axiom.
Focused verification is GREEN and the exact target is current (`9571/9571`).
`towerHeatSol_raw` and `towerHeatSol_any` are therefore theorem-level
**100% checked**, and their dedicated direct-tower machinery is **100%**.

The complete-noncompact Shi theorem remains theorem-level **0%** until the
independent solution-produced `ShiCutoffData` frontier is closed and consumed.
Unconditional HCG Theorem 3.10 remains
theorem-level **0%**; its dedicated consumer machinery is about **97%**.
