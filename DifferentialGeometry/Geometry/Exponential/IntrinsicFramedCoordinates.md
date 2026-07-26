# IntrinsicFramedCoordinates

## Purpose

This migration module implements Stages 1--3 of the accepted H6 radius architecture: Route A
for the canonical intrinsic geometry, combined with Route C at the H6 producer
boundary. It is intentionally temporary and must not become a second polished
normal-coordinate hierarchy.

## Status

Focused verification passes without diagnostics. The module now provides:

- `intrFrameCLM`, the normal-frame linear map re-continuousized in the fixed
  model norm on both sides;
- `intrinsicFramedExp`, the total intrinsic exponential in that frame;
- global smoothness in the vector variable;
- the value and manifold derivative at the origin;
- positive-ball agreement with the legacy chart-fixed `framedExpMap`.
- `intrFrameDiffeo`, the migration-only `C^1` branch obtained by restricting
  the old branch to the agreement ball; its inverse is definitionally the old
  framed chart;
- `intrFrameMetric`, the pullback metric of the total intrinsic framed map,
  together with its origin formula and agreement with the legacy pullback
  metric on the migration branch source.

The import DAG does not permit `FramedNormalCoordinates.lean` to import the
intrinsic exponential stack directly: that would cycle through Hopf-Rinow,
Gauss, injectivity, and framed coordinates. The migration therefore starts in
this higher file. The canonical names will be flipped only after the old local
branch has been moved below that cycle.

## Proof Notes

Two failed checks were representation issues, not failed mathematical routes.
An accidental `infinity` identifier first corrupted the `IsManifold` binder.
Then a direct composition used `normalFrame` with the Riemannian fiber norm
where `intrinsicFiber_smooth` expects the fixed model norm. The correct bridge
is the same underlying finite-dimensional linear map, packaged as
`intrFrameCLM : E ->L[Real] E`.

## Progress

- Stage 1 (total map and germ agreement): 100% proved and focused-checked.
- Stage 2 (temporary local branch transfer): 100% proved and focused-checked.
- Stage 3 geometry producer (total-map pullback metric): 100% proved,
  focused-checked, and exact-checked.
- Canonical intrinsic framed-API migration: about 35%; the HCG consumer switch,
  name flip, and intrinsic radius definitions remain.
- Sequence-uniform `NormalRadiusProfile` producer theorem: 0%; its dedicated
  zero-order Jacobi/Rm04 machinery remains about 99% complete.
- Native all-order metric-bound producer theorem: 0%; its dedicated jet
  machinery remains about 35% complete.
- Whole HCG compactness machinery: about 60%; the unconditional endpoint
  theorem remains 0%.

## Next Target

Resolve the HCG completeness boundary before switching
`C4/StepBInputs.normalCoordMetric`. The total intrinsic map requires the
metric-induced `PseudoEMetricSpace`, `IsContinuousRiemannianBundle`, and
`CompleteSpace` instances, while the current public `normalCoordMetric Y x`
and `NormalCoordMetricBoundInput` carry no `MetricComplete Y` argument. The
switch must thread completeness honestly (or move it into the producer
package); it must not hide a classical fallback or create a second coordinate
metric API. After that decision, redefine the existing HCG name through
`intrFrameMetric` and migrate its local formulas once.
