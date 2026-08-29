# CoordRm04Bridge

## Role

This file is the lowest native bridge between the standard lowered metric
curvature tensor and the Levi-Civita curvature operator.

## Route

- `rm04_eq_inner_riem` reuses `metricRm04StdAt_eq_chartRiemannCLM`.
- It then rewrites `riemannOp` with the existing
  `riemannOp_eq_chartRiemannCLM_apply` bridge.
- Static signature preflight confirmed that both bridges use the same
  `X Y Z W` curvature-slot order. The ambient `[I.Boundaryless]` instance
  supplies `BoundarylessManifold I M`, so no additional public hypothesis is
  needed.
- No metric-convergence or HCG namespace is imported.

## Status

The source implementation is complete. `rm04_eq_inner_riem` passed
warning-free focused verification, and the explicitly named module refresh
completed successfully. Thus the dedicated proof and checked producer artifact
are 100%. This closes the lowest tensor/operator compatibility bridge; it does not by
itself prove any sectional-to-Ricci or strict-volume endpoint. The bridge is
roughly 2% of the dedicated strict-volume rigidity branch and well below 1%
of the full Morgan--Tian/Poincare program.

The earlier rewrite/elaboration risk is discharged: the two-step bridge checks
in its canonical file and its exported artifact is current.
