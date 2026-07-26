# HeatEarlyNear

## Proved source boundary

`HeatEarlyNear.lean` defines the actual Bochner heat potential over
`(0,t/2] x B(x,sqrt t)` and proves its uniform source-Carleson estimate.
The scale computation is explicit:

`sqrt(t/2)^(-n) * sqrt(t)^n = sqrt(2)^n`.

Thus `heatEarlyNear_norm` has no observation-time-dependent constant.  It
uses the real Euclidean heat kernel, `SrcCarl`, and the real set integral; it
does not package the desired estimate as a structure field.

## Verification and frontier

Source-written while the coordinated named build was active; focused Lean
verification is pending.  The file contains no `sorry`, `admit`, axiom,
opaque declaration, or heartbeat override.

The remaining early `Y^0 -> C^0` contribution is the spatial complement of
`B(x,sqrt t)`.  Its proof needs Gaussian annulus decay together with a
quantitative finite-dimensional cover/volume count.  The endpoint
`ricci_flow_forward_unique` remains 0%.
