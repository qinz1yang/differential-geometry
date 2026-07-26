# ResidualCost

## Purpose

This module exports the explicit arbitrary-dimensional constructor ledger for
the direct curvature-tower route.  The recurrence itself now lives in the
lower `ResidualLedger` module so `TimeRecursion` can consume it without an
import cycle.  This module does not state or assume the missing
arbitrary-dimensional residual theorem.

## Route

`rmResidualCost d 0 = 12 d^2`.  The successor adds two copies of the previous
residual, the existing generic `commStarCost d k`, and the Christoffel-time
cost `d^2 (12 + 3k)`.  `rmTowerCost` then uses the exact coefficient shape
consumed by `nablaKReactionAt_le`.

The specialization theorem `rmResidualCost_three` proves that this recurrence
is exactly the existing checked `resStarCost`, rather than a newly chosen loose
bound.

The level-zero constructor is now separated from the three-dimensional
curvature identity.  `e0Field_cost_any` proves the exact arbitrary-index cost
`12 * card(Idx)^2`; `rmBaseReact` is a compatibility alias for the canonical
static `hamiltonRmReact`; and `e0Field_comp_any` proves that `e0Field` realizes
this reaction in every finite orthonormal basis.  None of these lemmas uses
Weyl-flatness or `Fin 3`.

## Status

The definitions, nonnegativity/specialization lemmas, and arbitrary-index
level-zero cost/component lemmas pass focused verification; the current exact
target is GREEN (`3799/3799`).  The arbitrary-dimensional global residual and
direct scalar tower are now exact-current as `rmResidual_cost` and
`towerHeatSol_raw`, using the explicit `rmTowerCost` coefficient.

The arbitrary-dimensional Hamilton identity and its fixed-basis solution
producer are now exact-current as `hamiltonRm04Id` and
`rm04Base_of_solution_any`.  The solution-facing level-zero join is
exact-current as `e0Residual` in `ResidualBase.lean`, with `rmResidual_zero`
retained as the existential compatibility wrapper.  The arbitrary-index fixed
successor and recursive capstone are exact-current as `resStarNext_spec` and
`rmResidual_cost`.

The ledger, level-zero algebra, global residual, and direct-tower machinery are
100% checked.  The whole complete-Shi producer remains theorem-level 0% only
at the independent solution-produced `ShiCutoffData` frontier.
