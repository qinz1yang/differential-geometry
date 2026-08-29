# IntrinsicFramedCoordinates

## Framed exponential ball containment

- `intrFrame_mem_eball` states that a framed intrinsic exponential endpoint
  lies in the ambient metric eball of radius `ENNReal.ofReal r` whenever the
  model-vector norm is smaller than `r`.
- The proof uses `intrinsicGeodesic_riemannianEDist_le` on the radial geodesic
  from time zero to one, then rewrites with `intrinsicGeodesic_zero`,
  `expMapIntrinsic_def`, `intrFrame_apply`, and `normalFrame_sqrt`.
- `IsRiemannianManifold.out` converts the intrinsic extended distance directly
  to ambient `edist`. No curvature hypothesis or radius-smallness assumption
  is introduced.
- This producer lets a curvature bound on an ambient metric eball supply the
  radial curvature hypothesis consumed by `intrInj_ge_cgt_on`.

## Verification

- The first focused check failed because the original conclusion used
  `Metric.ball` and explicit `riemannianEDist` while the theorem intentionally
  assumed only `PseudoEMetricSpace M`; that layer has no ambient `dist` API and
  the intrinsic-distance name was unavailable in this scope.
- The source is statically repaired to stay entirely at the `edist`/
  `Metric.eball` layer. The repaired file then passed a warning-free focused
  check, and the named module refresh completed successfully (3818/3818).

## Program status

- This is source-written supporting machinery, not either of the two P1b
  theorem endpoints. P1b remains zero of two exact endpoints.
- Dedicated P1b machinery remains about 92%; the whole P0--P9 infrastructure
  remains at the authoritative 15--25% estimate.
