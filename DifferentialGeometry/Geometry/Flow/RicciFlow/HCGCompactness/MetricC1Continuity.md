# MetricC1Continuity

## Goal

Prove time continuity at a regular time of every finite cumulative metric
derivative seminorm, without selecting a global frame and without forming a
tensor-valued map whose fibre varies with the spatial point.

## Route

The implementation fully evaluates each fixed-background covariant derivative
on slots from one genuine smooth local frame.  Local frame vectors are extended
to global smooth sections only near the point, the existing joint scalar tower
then gives continuity, a finite component-square bound produces a local norm
patch, and compactness turns the spatial cover into one uniform time
neighborhood.

The proposed extra partial-derivative continuity API is not needed:
`prodExtDerivAt_inf`, already consumed by
`covDerivOfField_eval_contMDiffAt`, supplies the parametric scalar derivative
step.

## Status

The lower scalar metric-pair producer has passed focused and targeted module
verification.  The complete local-to-global file passes focused verification:

- `metricCov_smooth` proves scalar spacetime continuity only after applying
  the varying-fibre tensor to actual local-frame slots;
- `metric_c_patch` turns the finite component square into one exact-order
  local modulus;
- `metric_c1_patch` intersects the order-zero and order-one patches;
- `metric_c_event` applies compactness to one arbitrary exact order;
- `metric_cp_tendsto` intersects the finitely many exact-order time
  neighborhoods and proves convergence in every cumulative order `p`;
- `metric_c1_tendsto` takes a compact finite subcover and intersects its time
  neighborhoods.

No `HasLocallyConstantChartAt`, global frame, whole-tensor equality, or new
consumer convergence hypothesis is used.

## Progress

The `metric_c1_tendsto` and all-finite-order `metric_cp_tendsto` theorems are
proved and focused-verified (100%); their dedicated local-to-global machinery
is complete (100%).  This closes the time-uniform metric-jet input needed by
the noncollapsing operator route.  The actual finite-spectral-support `A2(s)`
estimate remains unstated and unproved (0%).  Its dedicated machinery is now
approximately 77% complete: the live local analytic frontier is the
rank-generic arbitrary-input small-principal-coefficient `appCc` tame bound,
then specialization to the scalar Hessian/gradient decomposition.

## 2026-07-14 fixed-slab bounds

The fixed-slab boundedness distinction is now explicit.  `metricCov_cont`
proves fully applied scalar continuity at an arbitrary regular spacetime point
while the covariant-derivative background metric stays fixed.  The public
`metric_cp_bdd` then fixes one compact set `K ⊆ D.regular` first and returns an
order-indexed family of constants bounding every finite cumulative metric
seminorm uniformly on `K × M`.  No order-dependent shrinking of `K` occurs.
Focused verification passes without warnings.

This is a metric-jet producer, not yet the time-uniform lower-order pairing.
The remaining analytic frontier is to transfer these bounds to uniform
fixed-background jets of the exact mixed coefficient families
`scalarFluxCoeff q (G.metric t)` and `connTraceCoeff q (G.metric t)`, then feed
those envelopes into uniform versions of the balanced and slot-transport
pairings.  `scalar_crit_tame` remains unstated/unproved (0%); its dedicated
machinery is about 77%.  Perelman noncollapsing remains 0% with about 40%
dedicated analytic machinery, and whole HCG machinery remains about 53% with
endpoint theorems at 0%.
