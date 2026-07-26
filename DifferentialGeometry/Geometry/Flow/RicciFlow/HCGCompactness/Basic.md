# Basic

Source used: MSM135 Chapter 3, especially the pointed-solution and compactness-theorem statements. Chapter 4 was used only to identify the metric compactness/direct-limit backend as the proof frontier.

Introduced definitions: `PointedFlowData`, `PointedFlowSeq`, `CompleteInput`, `CurvBoundInput`, and `InjInput`. The metric-only pointed Riemannian definitions now live in `PointedRiemannian.lean`.

2026-07-09: removed the arbitrary numeric `NoncollapseInput`.  Canonical volume
noncollapse now uses `FlowBaseVolData` plus `IsFlowBaseVolBound` in
`NoncollapseInjectivity.lean`, based on actual metric balls and Riemannian
volume.  The real compactness theorem continues to consume `FlowBaseInjBound`.

Existing APIs found: RicciFlower already has `RicciFlow.SolutionOn`, `RicciFlow.IsSolutionOn`, `Realized.RealTimeInterval`, and canonical lowered curvature via `S.base.rm04`. The HCG injectivity-radius layer now uses the normal-coordinate backend; only the legacy `InjInput` remains for older wrappers.

2026-05-28 legacy-input clarification: `InjInput` and `NoncollapseInput` are explicitly compatibility baggage. `InjInput.injRadiusAtBase` is not connected to the normal-coordinate injectivity radius, and `NoncollapseInput.volumeAtBase` is not yet tied to a formalized Riemannian volume computation. New compactness statements should use `FlowBaseInjBound`, not `InjInput`.

Update: `PointedFlowData.atTime`, `PointedFlowSeq.atTime`, and `PointedFlowSeq.atZero` now expose the pointed Riemannian time slices needed for MSM135 Theorems 3.9 and 3.10.

2026-05-27 review update: the metric time-slice object was renamed from `PointedMetricData` to `PointedRiemannianManifold`, since it bundles an underlying carrier, manifold structure, basepoint, and smooth Riemannian metric. The public pointed Riemannian and pointed-flow records no longer store a `smoothPlus` field; the few Ricci-flow API calls that need `∞ + 1` derive it locally from the stored `IsManifold I ∞` instance.

2026-05-27 completeness update: removed the primitive `MetricComplete` axiom from `Basic.lean`. The pointed Riemannian metric layer was split into `PointedRiemannian.lean`, where `MetricComplete` is defined using the Riemannian emetric induced by the stored smooth metric. `CompleteInput` now means completeness of each time-slice metric, not an arbitrary `Nat -> Real -> Prop`.

Verification: passed. Early failures were mechanical instance/universe issues in the new records; they were fixed by using the stored manifold instances and explicit universe parameters.

2026-07-17: added the checked projection `CompleteInput.at_time`.  It turns
flow completeness at a chosen carrier time into `SeqMetricComplete` for the
corresponding pointed time-slice sequence.  This is the first concrete
reduction used inside the book-facing `compactnessSol` proof; it introduces no
new completeness predicate.
