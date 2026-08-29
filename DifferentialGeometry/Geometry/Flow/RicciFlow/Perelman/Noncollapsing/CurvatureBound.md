# Scalar bounds from controlled curvature

## Role

`FlowMetricBall.IsRmControlled` bounds the squared Riemann-curvature norm on
the ball's parabolic cylinder.  Scalar curvature estimates used by the
noncollapsing argument should be derived here from that native norm bound.

## Results

- `scalar_le_of_rm` gives the existing upper scalar-curvature bound.
- `scalar_ge_of_rm` is the symmetric lower bound, obtained from the same exact
  Riemann-norm normalization and `scalar_abs_le_rm`.  It does not assume a
  scalar-curvature estimate separately.

## Verification

The lower bound is source-written; focused verification is pending the shared
elaboration window.

## Next leaf

Use `scalar_ge_of_rm` along the range supplied by `lRegRange_scale` to bound
the negative scalar contribution to the small-source L-action.  The separate
metric-to-volume comparison remains the next lower-layer measure frontier for
`redVolume_ball_le`.
