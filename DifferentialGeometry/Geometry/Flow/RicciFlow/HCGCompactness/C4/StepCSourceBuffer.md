# StepCSourceBuffer.lean - uniform intrinsic source buffers

## 2026-07-18 framed migration status

All fixed-center source charts and coordinate-buffer statements in this file
now use `framedChartAt` / `framedExpDiffeo`; the radius backend is the canonical
`expRadiusGp`.  The only remaining raw exponential-radius names occur inside
the low-level proof that a framed source point belongs to the underlying raw
exponential kernel, transported through `normalFrame_sqrt`.  Source migration
is complete.  Focused Lean verification passes against the exact-refreshed
canonical Stage-C prerequisites, and this module's own exact target refresh
completed successfully in the coordinated Stage-DAG write chain.

## 2026-07-16 verified first-exit producer

The new file is focused-green and warning-free.  It converts the fixed
coordinate closed-ball buffers retained by `HasSuppConvData.buffer_cover` into
one positive intrinsic radius, uniform in the retained source slot and in every
stage of the extracted subsequence.

The reusable geometric step is `NormalCoordMetricEquivOn.ball_core_dist`.
It uses the selected minimizing join and a first-exit argument to prove that
the whole join stays in the coordinate closed ball.  It therefore returns both
membership in the smaller normal-coordinate core and the quantitative estimate

```text
dist (chi x) z <= sqrt 2 * (riemannianEDist I (chi.symm z) x).toReal.
```

`NormalCoordMetricEquivOn.ball_subset_core` is the inclusion-only projection.
The private prefix estimate `chart_join_le` is needed because the selected
`minimizingVec` API does not identify a prefix of one chosen minimizing join
with a separately chosen join to the intermediate endpoint.

`HasSuppConvData.metric_buffer` keeps the source slot and coordinate center
chosen by `buffer_cover`.  For every point of the proper-metric intrinsic ball
it returns core membership and the stage-distance version of the same
coordinate estimate.  Its proof consumes the already retained `geom_on`
normal-metric and canonical `expRadiusGp` controls plus `RealizesEdist`; it adds no
endpoint-radius assumption and no field to `MetricCompactnessInputs`.

## Remaining frontier and accounting

The intrinsic-buffer producer in this file is complete and canonical-framed
focused- and exact-green (100%).  The dedicated
global-injectivity machinery is approximately 85%: local chart injectivity,
the two-sided return tail, and the uniform intrinsic/coordinate buffer are now
checked, while the finite buffered-cover `InjOn` assembly is not yet stated and
is therefore 0% as a theorem.  That assembly now looks like routine finite
cover and triangle-inequality work rather than a missing analytic API.

The concrete `MetricCompactBase.exists_b1_raw` theorem now has a complete proof
body, but its framed chain is not yet green.  The separately named textbook
Step B1 theorem and all unconditional HCG compactness endpoints remain
theorem-level 0%.  Rounded project machinery estimates remain about 95% for
Step-B/B1, 87% for Chapter 4, and 60% for the whole HCG program; these
infrastructure percentages are not endpoint theorem completion.
