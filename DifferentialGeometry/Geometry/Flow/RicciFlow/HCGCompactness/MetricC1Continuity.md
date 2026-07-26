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
  neighborhoods;
- `metric_c1_span` proves one uniform varying-background order-one modulus on
  every compact regular-time slab.

No `HasLocallyConstantChartAt`, global frame, whole-tensor equality, or new
consumer convergence hypothesis is used.

## Progress

The fixed-background `metric_c1_tendsto`, all-finite-order
`metric_cp_tendsto`, and varying-background `metric_c1_span` theorems are
proved and focused-verified (100%).  Their dedicated local-to-global metric
modulus machinery is complete (100%).  The noncollapsing endpoint is still
unstated and unproved (0%): the next exact producer is the target-length
Galerkin theorem `gal_span`, followed by `gallim_on`, target-length
positivity/mass, and the finite interior Good-set induction.

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

## 2026-07-18 varying-background span

`metric_c1_span` now passes focused verification.  It quantifies over the
background time before any spectral type is formed and returns one positive
radius uniform in both times and all spatial points on a compact regular-time
slab.

The proof remains scalar throughout.  In one canonical coordinate frame it
expresses the order-zero norm through the Gram matrix and its inverse, and the
order-one component through scalar spatial derivatives and the coordinate
Koszul formula for the varying Levi-Civita connection.  Compactness first
turns the local spatial patches into a uniform neighborhood of one diagonal
time, then a finite cover of the compact time slab supplies the global radius.
No equality of whole tensors in varying fibres, global frame, endpoint
regularity upgrade, or new consumer hypothesis is used.

Honest accounting: `metric_c1_span` is theorem-level 100%, and its dedicated
varying-background modulus machinery is 100%.  This is one geometric producer,
not the noncollapsing theorem: `gal_span`, `gallim_on`, the target-length
positivity/mass package, the finite Good-set induction, `NoLocalCollapsing`,
and `ham3_noncollapse` remain theorem-level 0%.  Whole HCG machinery remains
about 60%.
