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
derivative and Christoffel time derivative. The proof is sorry-free; focused
verification and the targeted module build passed.

This closes the all-level time/space swap machinery. The next frontier is the
solution-facing residual assembly.

`tailTowerData` now supplies that positive-tail adapter directly from
`IsSolutionOn`: it chooses the actual level-zero curvature derivative, uses the
Christoffel evolution RHS, proves the orthonormal-frame book identity, and
packages `frameTowerSwap`. Focused verification and the targeted module build
passed. Together with `rm04Base_of_sol`, it discharges every standing input of
`resStarBoundLF`.
