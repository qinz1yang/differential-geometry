# TowerNormRegularity

## Result

`towerNorm_joint` proves joint spacetime `C-infinity` regularity of every
intrinsic squared norm `|nabla^k Rm|^2` on the regular set of a Ricci-flow
solution. The proof uses coordinate inverse-metric smoothness, the coordinate
curvature tower, and the coordinate contraction formula for `normSq0S`.

## Status

The theorem is **100% complete**, focused-check green, and exported by a
targeted build.  Its accidental `[CompactSpace M]` hypothesis has been removed
through the chart-local coordinate regularity chain.  It now supplies the
closed-slab continuity input for both the old compact producer and the
complete-noncompact assembly in `HCGCompactness/MovingShiOpen.lean`.

This regularity result does not prove the heat inequality or the complete
maximum principle; those remain the separate `exists_rmTowerSol` and
`BernsteinTower.estimate_complete` frontiers.
