# SolutionTowerHeat

## Purpose

Produce the solution-level `TowerHeatBoundOn` inequality on a strictly
positive-time tail in dimension three.

## Route

At each target `(t,x)`, reindex `smoothOrtho_local` by
`Fin 3 equiv Fin (finrank E)`. Use `resStarSol` for the fixed-cost residual,
`tailFrameTimeReg` and inverse uniqueness for the moving inverse metric,
`nablaKNormHeatAt` for the intrinsic time derivative, and
`nablaKReactionAt_le` for the reaction estimate. The output coefficient is
`towerSolConst k`, built from `resStarCost k`.

## Status

`towerHeatSol` is proved, focused-check green, and exported by a targeted
build. The theorem and its dedicated machinery are both **100% complete**.
It is consumed by `HCGCompactness/MovingShiProducer.lean`; the remaining work
there is endpoint assembly, not another curvature heat-equation input.
