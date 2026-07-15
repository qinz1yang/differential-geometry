# TailFrameRegularity

This module packages the full metric-frame spacetime regularity available on a
strictly positive tail of a Ricci-flow solution.

The key point is that the new closed-left carrier `[t0, omega)` lies inside the
original regular interval `(alpha, omega)`.  Therefore the original solution's
joint metric-frame smoothness applies even at the new left endpoint.  The
fixed-base space/time derivative field is supplied by the Ricci-flow equation
and `metricFrameComp_fixedBaseSwap_of_solution`.

Status: focused verification passed. The theorem constructs the positive-tail
metric-frame spacetime regularity package from `IsSolutionOn`; it does not
assume that package as a new blackbox.
