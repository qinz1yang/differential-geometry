# TubeStability

## 2026-07-15

This low ODE layer now proves the first-hit lemma, joint small-error continuity
of `gronwallBound`, and
`integralCurve_tendstoUniformlyOn_of_limit_tube`.

The tube theorem is verified without a stage-family containment assumption.  A
first-exit time is selected for the distance to the limit curve, Mathlib's
time-dependent-set Grönwall comparison is applied only up to that time, and the
result contradicts the chosen tube radius.  The parameter type and controlled
set carry no topology or compactness assumptions.

The theorem is the complete generic `C⁰` estimate.  It is infrastructure for
`MapCInfConvOnCompacts.ode_solutionAt`, not a proof of that all-order endpoint.
The next producer is compact graph/tube packaging that derives its uniform
field and Lipschitz hypotheses from compact-open map convergence.
