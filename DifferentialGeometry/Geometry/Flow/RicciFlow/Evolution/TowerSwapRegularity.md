# TowerSwapRegularity

## Purpose

Close the recursive time/space derivative swap for all local-frame curvature
tower levels without adding a swap hypothesis.

## Route

`frameTowerSwap` performs one simultaneous induction. At level `k`, the
already-produced fixed-base swap and time derivative feed
`covDerivStepComp_hasDerivWithinAt`; `frameTowerSmooth` plus
`fixedBaseOnRegSmooth` then produce the level-`k+1` swap.

The only theorem-facing inputs are the genuine level-zero curvature time
derivative and Christoffel time derivative. The former `[CompactSpace M]`
binder on `frameTowerSwap` was artificial and has been removed without changing
the rest of the statement or proof.

This closes the all-level time/space swap machinery. The next frontier is the
solution-facing residual assembly.

`tailTowerData` now supplies that positive-tail adapter directly from
`IsSolutionOn`: it chooses the actual level-zero curvature derivative, uses the
Christoffel evolution RHS, proves the orthonormal-frame book identity, and
packages `frameTowerSwap`. Its former `[CompactSpace M]` binder was likewise
artificial and has been removed. Together with `rm04Base_of_sol`, it discharges
every standing input of `resStarBoundLF`.

The source audit found no deeper compactness-dependent API. After the refreshed
`FrameTowerRegularity` artifact became available, this file passed its focused
check without diagnostics.

## General-interval germ adapter

`towerDataAt` now removes the positive-tail shape from downstream callers. For
an arbitrary `SolutionOn D`, a regular time `t`, and a smooth orthonormal local
frame, it chooses a compact regular window and an internal positive tail, calls
`tailTowerData`, and transports ordinary derivative germs back to the original
solution and `D.carrier`.

Its output is deliberately the raw component API consumed by the residual
recursion: `frameComp0S`, `christoffelSymbolInFrame`, and `iteratedRmComp`.
There is no import of `TimeRecursion`, no new regularity hypothesis, and no
parallel tower definition. The theorem passed its focused check without
diagnostics and is exact-current through the dedicated target (`9516/9516`).

Theorem accounting: `towerDataAt` is 100% checked. It is an adapter for the
residual capstone; `rmResidual_cost` and `towerHeatSol_raw` are now separately
100% checked as well.
