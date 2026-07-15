# IteratedRmTowerHeatEq

## Pointwise heat producer

`nablaKNorm_smooth` derives fixed-time spatial smoothness of every intrinsic
curvature-tower norm from the arbitrary-valence tensor norm API.
`nablaKNormDu`, `nablaKNormHess`, and `nablaKNormLap` are the canonical scalar
differential, Hessian, and intrinsic Laplacian objects.

`nablaKNormHeatAt` is the local interface needed by the BBS assembly. At one
regular time and point it chooses smooth global extensions of the supplied
tangent basis internally and discharges all scalar realization hypotheses. Its
only noncanonical inputs are the actual component time derivatives of the
inverse metric and of `nablaKRm04Field` at that point.

The older global `nablaKRm04NormHeatEquationOn_intrinsic` interface remains
available for compatibility. The pointwise theorem avoids demanding one
global basis and global derivative data when the geometric producer is local.

Focused verification passes. The next consumer is the solution-level
StarSum/Bernstein assembly combining `resStarSol` and `tailFrameTimeReg`.
