# SolutionCompactness

## 2026-07-09 canonical consumer

`solutionComp_of_mc` is now the canonical theorem-facing consumer. It takes a
specific `MetricCompactnessConclusion (X.atZero)` and concrete
`FlowUpgradeData X mc`; it neither invokes the unconditional
`metricCompactness` frontier nor accepts the desired conclusion as input.

The zero-callsite legacy APIs `SmoothFlowLimitInput`,
`smoothFlowLimitInput_of_flowLimitData`, and `solutionCompactness` were removed.
They accepted the desired compactness conclusion through an `upgrade` field and
therefore obscured rather than solved the flow-compactness producer frontier.

This consumer refactor is 100% complete. The checked conditional consumer is
100%, while unconditional Theorem 3.10 remains 0%; its dedicated producer
machinery is tracked separately in the P4 notes. The project-wide endpoint
remains 0%, and the current HCG machinery estimate is about 45%.

The material below predates the 2026-07-09 removal and is retained only as
historical design context.

Source used: MSM135 Definition 3.6 and Theorem 3.10, with the Pro review warning that curvature bounds alone do not supply the derivative-estimate backend in Lean.

Introduced definitions: `SmoothFlowLimitInput` and `solutionCompactness`.

Design note: `solutionCompactness` reduces through `metricCompactness` applied to `X.atZero`. It explicitly requires `FlowDerivativeInput` and `SmoothFlowLimitInput`; it does not pretend that `SpacetimeCurvBound` alone proves smooth Cheeger-Gromov-Hamilton convergence.

2026-05-27 review update: after the pointed Riemannian rename, `solutionCompactness` still reduces through `metricCompactness` on `X.atZero`.

2026-05-27 injectivity update: `solutionCompactness` now carries `[I.Boundaryless]` because `FlowBaseInjBound` unfolds through the normal-coordinate injectivity-radius backend at time zero.

2026-05-27 bounded-geometry correction: after replacing the curvature-bound axioms with concrete norm definitions, `solutionCompactness` names the time-zero bounded-geometry projection explicitly before applying `metricCompactness`. This avoids stale or ambiguous implicit-argument elaboration around the updated `SeqBoundedGeometry`.

2026-05-28 all-times-bounds clarification: `FlowDerivativeInput` still does not provide the full mixed `partial_t^q nabla^p g(t)` estimates from MSM135 Lemma 3.11. Those estimates remain part of the explicit `SmoothFlowLimitInput` backend until the all-times bounds and spacetime Arzela-Ascoli layer are formalized.

Verification: focused checking passed and the targeted module refresh passed.
