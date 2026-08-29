# SegmentBallContinuity

## Positive-radius continuity

`segBall_vol_cont` reuses the checked polar formula `segBall_area_eq`.  After
that rewrite, changing the radius changes only the indicator of the tangent
`gBall`.  The exceptional level set is the image of a norm sphere under the
normal-frame linear equivalence, hence is null for the chart-model Haar
measure.  Dominated convergence is bounded by one fixed, slightly larger ball;
its integral is finite by `segBall_vol_fin`.

Focused verification passed without warnings after the local empty-line style
cleanup.  The named module artifact was refreshed for downstream auditing, and
the public theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.
