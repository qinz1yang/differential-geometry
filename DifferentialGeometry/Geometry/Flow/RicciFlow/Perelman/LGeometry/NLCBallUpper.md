# NLCBallUpper

## Role

This module proves the controlled-ball upper bound for reduced volume used in
the good/bad L-exponential-source split.  It combines genuine endpoint
localization, a curvature-produced scalar lower bound, the pulled-back
Jacobian formula, moving-volume comparison, and the exactly normalized source
Gaussian tail.

## Checked producers

- `lRedLen_scale` obtains the lower bound
  `-finrank^2 * eps <= redLength` for minimizing small-source endpoints.  Its
  proof uses `lRegRange_scale`, `scalar_ge_of_rm`, the nonnegative kinetic term,
  and the action/cost identity; no reduced-length bound is assumed.
- `lRedDen_scale` converts that length bound into the explicit pointwise
  reduced-density upper bound.
- `lRedJac_ball_le` changes variables through `lExpPartial` and bounds the
  small-source integral by the explicit density constant times the moving
  volume of the controlled terminal ball.
- `ballVol_move_le` applies the second quadratic-form comparison from
  `lMetric_scale` to `volumeMeasure_le`, giving the fixed determinant factor
  `sqrt((4/3)^finrank)`.
- `redVolume_ball_eta` partitions the full strict minimizing domain into the
  closed small-source part and its open complement.  The first part uses the
  preceding two estimates; the second uses `lRedJac_tail_le` and the
  dimension-uniform exact Gaussian threshold `lSrcGauss_unif`, contributing at
  most an arbitrary prescribed positive `eta`.
- `redVolume_ball_le` is the compatibility specialization `eta = 1/4`.

Focused verification is warning-free green, and the named module artifact was
refreshed successfully.  The implementation contains no `sorry` or `admit`.

## Quantifier boundary

Both public ball estimates are deliberately fixed-terminal-time
compact-backward-slab theorems: `time` and its regular slab are inputs before
the theorem produces
`eps0`.  This is the strongest statement justified by the checked
`lExp_scale_ball`, whose `eps0` is likewise produced after fixing terminal
time.  The proof does not commute `exists eps0` through `forall time` and does
not assume endpoint containment or noncollapse.

The arbitrary-tail obstruction is now removed. The remaining localization
leaf for a global smooth-noncollapsing constant is a terminal-time-uniform
endpoint/ball estimate on the half-open interval. A finite cover does not
apply to `[a, omega)`. The current threshold ultimately uses the global
compact-slab scalar-gradient constant in `lGrad_scale`.

The lowest missing native producer is `shiRm1_ball`, a scale-invariant first
curvature-derivative estimate on a strictly smaller cylinder inside an
Rm-controlled parabolic ball. Its immediate L-geometry adapter is
`lGrad_ball`, with the necessary later-half-time and half-radius losses. The
existing checked Shi producers all assume a whole-manifold curvature bound and
conclude on `Set.univ`; restriction/pullback modules do not create a bound from
ball control. Once `shiRm1_ball -> lGrad_ball` exists, this domain-split proof
can be reused after the local speed, metric, range, and exponential adapters to
choose one `eps0` before terminal time.

## Progress accounting

- `redVolume_ball_le`: 100% for its stated fixed-terminal compact-slab
  interface.
- `redVolume_ball_eta`: 100% for arbitrary positive Gaussian-tail error.
- Dedicated good/bad source localization machinery at that interface: 100%.
- Terminal-time uniformization needed by the global `smooth_nlc` assembly: 0%
  as a theorem; its fixed-time inputs are complete.
- `shiRm1_ball` and `lGrad_ball`: unstated and unproved, 0% theorem endpoints.
- `smooth_nlc`: unstated and unproved, 0%.  The ball-upper and compact
  reduced-volume-floor branches are infrastructure and are not counted as
  completion of that endpoint.
- Under the full P0--P9 denominator, the final `poincare_of_inputs` theorem
  remains 0%; full-program infrastructure remains approximately 15--25%.
