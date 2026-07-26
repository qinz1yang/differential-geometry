# OpenWindowEquiv

## Purpose

`OpenWindowEquiv.lean` owns only the order-zero time-direction estimate needed
by the P4 producer.  It converts the uniform Riemann-curvature bound on one
canonical compact window into:

- a Ricci quadratic coefficient chosen before the sequence member;
- a finite majorant for the exponential metric-equivalence factor; and
- uniform equivalence of every member's time-slice metrics to its time-zero
  metric on that window.

This is separate from complete-noncompact Shi estimates, varying-source
covariant induction, Step-D provenance, and bump localization.

## Current status

The theorem `CurvBoundInput.metricEquiv_open` is focused GREEN.  It uses the
existing arbitrary-dimensional Ricci trace bound and the checked Ricci-flow
metric-equivalence theorem; it introduces no new geometric hypothesis.  The
only repair needed after the upstream refresh was to expose the let-bound
`timeRadius` before rewriting absolute values and to name the upper-window
projection explicitly in the nonnegative-time branch.

The calls to `CurvBoundInput.bound_on_window`,
`twoTensorQuadBound_of_solutions`, and
`metricUniformEquivalentOnWindow_of_solutions'` retain the intended
constants-first quantifier order.  The theorem is 100% source-checked; its
exact artifact is also current after the narrow refresh required by
`ConvFieldCanon`.  The unconditional `compactnessSol` endpoint remains 0%,
while whole-HCG supporting machinery remains approximately 60%.
