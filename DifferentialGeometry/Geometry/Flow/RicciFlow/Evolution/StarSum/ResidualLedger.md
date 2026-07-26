# ResidualLedger

## Purpose

This lower module owns the arbitrary-dimensional constructor-cost recurrence
shared by the time recursion and the final residual package.  Moving the ledger
below `TimeRecursion` avoids an import cycle while preserving the public names
`rmGammaCost`, `rmResidualCost`, and their nonnegativity lemmas.

## Status

The module is focused-green and exact-current through the verified downstream
`TimeRecursion` refresh.  The ledger itself is 100% checked infrastructure.
The successor and solution-only capstone are now exact-current as
`resStarNext_spec` and `rmResidual_cost`; the direct scalar tower is exact-current
as `towerHeatSol_raw`.
