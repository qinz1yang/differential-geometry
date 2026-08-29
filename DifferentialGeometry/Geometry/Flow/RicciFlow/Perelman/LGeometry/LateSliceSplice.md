# Uniform early-slice splicing

`LateSliceSplice.lean` isolates the downstream part of the Morgan--Tian
initial-slice argument.  It does not assume or prove the missing existence of a
point with reduced length at most `n / 2`.

## Results

- `lRampAct_fwd` chooses Gram and scalar constants on one fixed compact forward
  time slab.  The constants are uniform over every bounded terminal time and
  every affine chart ramp whose forward-time image stays in that slab.
- `redLen_ramp_bound` splices such a ramp onto a concrete minimizing regularized
  L-ray.  A reduced-length upper bound at the ray endpoint becomes an explicit
  reduced-length upper bound at every target coordinate in a compact convex
  chart set.
- `redLen_ball_bound` specializes the target to a coordinate ball, bounds every
  endpoint displacement by its diameter, and returns the inverse-chart open
  ball as a measurable set of strictly positive Riemannian volume.

The second theorem is the actual action estimate needed after an
`exists_redLen_le` witness becomes available.  Compactness of the manifold must
still select finitely many convex chart targets with a uniform positive volume;
that is separate from the all-point spacetime barrier needed to produce the
initial witness.

## Verification

Focused verification passed without warnings.  The file contains no `sorry`,
`admit`, or added axiom.  Its named artifact was refreshed successfully.

## Remaining initial-slice inputs

This file removes the local action/splice step.  The later uniform reduced-
volume floor still needs:

1. the genuine `exists_redLen_le` producer, hence the all-point spacetime weak
   upper barrier across the cut locus;
2. a finite compact-manifold chart selection turning the local balls here into
   finitely many choices with a uniform radius and a uniform positive lower
   bound for their time-`a0` Riemannian volumes;
3. the elementary specialization `c = sqrt (T - a1)` and
   `b = sqrt (T - a0)`, including uniform lower control of `b - c` and upper
   control of the explicit bound for `T` in the half-open terminal interval;
4. application of `redVolume_set_low`, followed by the checked reduced-volume
   monotonicity and the independent controlled-ball upper estimate.

## Progress

`redLen_ramp_bound` is the complete local splice/action brick.  It accounts for
roughly 20--25% of the dedicated late-time-floor machinery, while
`redVolume_late_low`, `smooth_nlc`, the P2 theorem endpoint, and the final
Poincare theorem remain 0% until their declarations are proved.
