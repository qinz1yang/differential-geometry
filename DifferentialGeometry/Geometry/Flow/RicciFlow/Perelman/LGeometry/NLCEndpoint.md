# Endpoint localization for the small-source branch

## Role

The small-source half of the reduced-volume localization argument must show
that a regularized L-ray whose source vector is controlled reaches the chosen
terminal flow-metric ball.  The final step of that argument is metric rather
than curvature-theoretic: a fixed terminal-metric energy budget bounds the
endpoint distance.

`NLCEndpoint.lean` isolates that step without assuming the desired containment.

## Results

- `lGrad_scale` uses the native compact-slab producer `lGrad_bound` and turns
  its uniform constant into the inverse-cubic form `A / r^3`, uniformly for
  every `0 < r <= rho`.  This is the scalar-gradient scale needed in the
  small-source speed bootstrap for the compact smooth-flow theorem; it assumes
  no gradient estimate.
- `lRegRicci_le` derives, directly from `FlowMetricBall.IsRmControlled`, the
  Ricci quadratic bound required by `lRegSpeed_gron` at every curve point that
  is still in the controlled parabolic ball.  It uses the native
  `ricci_quad_sol` trace estimate and the exact coefficient
  `finrank(E)^2 * sqrt (1 / radius^4)`.
- `lRegSpeed_ball` combines `lGrad_scale`, `lRegRicci_le`, and
  `lRegSpeed_gron`.  It produces the quantitative regularized-speed bound on
  any curve segment before its first exit from the controlled parabolic ball;
  it assumes neither a scalar-gradient estimate nor a Ricci estimate.
- `lMetric_scale` compares every metric on a shorter parabolic interval with
  the terminal metric using the explicit factor `exp (2 A eps r^2)`, uniformly
  over all radii bounded by one fixed regular slab.
- `lRegSpeed_scale` is the scale-uniform, prefix-local speed producer.  At a
  time `s`, it needs moving-ball containment only on `Icc 0 s`, which is the
  information available in a first-exit argument.
- `lExp_edist_le` specializes the native Riemannian energy-distance estimate to
  a regularized L-ray.  A terminal-metric energy bound `C` gives endpoint
  distance at most
  `sqrt (sqrt tau) * sqrt C`.
- `lExp_mem_ball` turns the strict version of that quantitative bound into
  membership in `FlowMetricBall.set`, whose metric is exactly the terminal
  metric at the ball time.
- `lRegRange_scale` performs the first-exit argument.  Its internally chosen
  scale gives a strict energy margin even when the first exit is the right
  endpoint, and it concludes both terminal half-ball containment and moving
  `B.setAt (T - s^2)` containment throughout the interval.
- `lExp_scale_ball` is the endpoint corollary at backward time
  `eps * B.radius^2`.

Both results are genuine producers from curve energy; neither takes endpoint
containment as an input.

## Verification

The endpoint energy-to-distance results, curvature-to-Ricci input,
scaled-gradient producer, metric-scale comparison, prefix-local speed theorem,
and first-exit range/endpoint theorems have passed focused, warning-free
verification.  The named `NLCEndpoint` module refresh also passed, so these
exported declarations are available to downstream localization modules.

## Remaining leaf

The next small-source leaf is the reduced-length lower bound along the
contained minimizing rays.  The native Riemann-norm
bound now supplies the needed scalar lower bound in `CurvatureBound`; the
nonnegative kinetic term then leaves an explicit `O(eps)` lower bound for
reduced length.  The final ball upper estimate will combine that density bound,
the L-exponential change of variables, moving-to-terminal volume comparison,
and the already checked source-Gaussian tail.

A genuinely local, noncompact version would still require a local
first-derivative Shi estimate on a smaller parabolic ball.  The current native
Shi theorem is global and assumes completeness plus a whole-manifold curvature
bound, so it cannot be inferred from `FlowMetricBall.IsRmControlled`.  That
larger API gap does not block the compact `smooth_nlc` route and is not encoded
as a consumer hypothesis here.

## Honest progress

- Endpoint energy-to-distance and energy-to-ball conversion: 100%.
- Curvature-to-Ricci and compact-slab scaled-gradient inputs for the L-speed
  bootstrap: 100% each.
- Prefix-local moving-speed and full first-exit range containment: 100%.
- Dedicated curvature-driven small-source containment machinery: about 85%
  complete, with downstream reduced-length and integral assembly still
  outstanding.
- `redVolume_ball_le`: not yet proved, 0%; its dedicated localization machinery
  is about 55% complete when the independent source-Gaussian tail and pending
  metric-volume comparison branches are included.
- `smooth_nlc`: not yet proved, 0%.  This remains an early analytic leaf of the
  broader Poincare program, whose total completion is still only a few percent.
