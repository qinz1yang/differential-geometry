# NormalPhaseSym

## Role

This file retains the negative-time half of the normalized Picard family so
that the launch time is an interior point for geometric realization and
geodesic uniqueness.  The time-one endpoint and its quantitative approximation
are unchanged.

## Current state

- `exists_normal_biflow` constructs a common exact normal phase flow on
  an interval strictly wider than `[-1,1]`, exposes the public closed-interval
  and ordinary interior derivatives, retains phase-box confinement, and proves
  the same forward `ApproximatesLinearOn` estimate.
- The retained time-one endpoint is jointly `C^infinity` in the initial phase
  point on the exact quantitative source ball.
- ODE uniqueness on the wider interval and `normalAccel_zero` prove
  `Phi 0 1 = 0`, so the explicit target ball is centered at the fixed model
  origin.
- Focused verification and the targeted module build passed; the new file has
  no local warnings or `sorry`.

## Frontier

This ODE-side producer is complete for the current branch.  The remaining work
is the HCG-side branch/readout transport and concrete finite-hat containment;
it is not another flow-regularity problem.
