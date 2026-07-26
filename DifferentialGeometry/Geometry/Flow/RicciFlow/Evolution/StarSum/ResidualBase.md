# ResidualBase

## Purpose

`ResidualBase.lean` is the solution-facing join between the arbitrary-dimensional
Hamilton evolution and the quantitative `StarSum2` ledger.  It stays separate
from `ResidualCost.lean`, which owns only the cost algebra and reaction
realization.

## Current status (2026-07-22)

- `e0Residual` is the fixed-witness level-zero producer for the direct
  arbitrary-dimensional residual recursion.  `rmResidual_zero` remains the
  existential compatibility wrapper.
- The fixed witness is the canonical `e0Field`; its cost is exactly
  `rmResidualCost (Fintype.card Idx) 0`.
- The proof consumes `rm04Base_of_solution_any`, `e0Field_cost_any`, and
  `e0Field_comp_any`; it introduces no new geometric or regularity assumption.
- Focused verification of the fixed-witness API is GREEN with no diagnostics;
  the exact target is current (`3802/3802`).
- Its axiom audit is the standard `[propext, Classical.choice, Quot.sound]`.

## Remaining frontier

The arbitrary-index fixed successor, global recursive residual capstone, and
direct scalar tower are now exact-current.  The level-zero producer is 100%,
`rmResidual_cost` is 100%, and `towerHeatSol_raw` is 100%.  The next independent
complete-Shi frontier is the concrete solution-produced `ShiCutoffData`, not a
further residual-field assumption.
