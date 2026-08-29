# RicciBound

## Status

`ricci_ge_of_rm` projects `FlowMetricBall.IsRmControlled` to the pointwise
Ricci quadratic lower bound needed by the localized Calabi/Jacobi chain. It
uses the generic comparison theorem `ricciLowerAt_of_rm` and does not add a
new curvature predicate.

`ricci_abs_of_rm` projects the same ball-local Riemann bound to the absolute
Ricci quadratic estimate used when differentiating lengths under the flow. It
reuses the generic `ricci_quad_sol` theorem.

Focused verification is warning-free GREEN.

## Next theorem

Use `ricci_abs_of_rm` along both the radial minimizing segment and the shortened
Calabi tail to localize the time-derivative part of the distance upper support.
The spatial Calabi data is already supplied by `exists_ballCalabi`.
