# FiniteHornRayRegularity

Owner: Chapter25 continuation; claim 3a1a4d7e-d3d3-47c6-9781-9f7c09841dbb.
Verified 2026-09-09 16:01 UTC: focused3 EMPTY (26.940s), named1 own leaf
lint-clean (51.405s), fresh audit1 (24.065s), public endpoint standard-only.
SHA256 8f827ef5012788b2c64f1b8cab101de240fe152f2074a8f77b26fc4e689255d0.
Named build replays existing skeleton obligations; the new instantiated
endpoint has no transitive proof placeholder.

Target: actual EndRay representatives are smooth and satisfy the original
metric geodesic equation on a uniform near-end open parameter interval.
FiniteHornLocalCompletion supplies an auxiliary complete metric agreeing on
an open neighborhood and preserving every local distance. A two-sided metric
segment is one intrinsic geodesic by CompleteTriangleEquality. Transfer its
smooth germ to the actual ray, then transfer the geodesic equation back by
local equality of chart Christoffel symbols. The auxiliary metric is used
only in a private proof; no completeness or regularity is added to EndRay.

Keep the auxiliary Riemannian metric instances inside a separate private
lemma whose hypotheses use explicit riemannianEDistOf. This avoids changing
the original horn metric or the completion instances attached to EndRay.
Its context must contain only TopologicalSpace/T2Space, not the original
MetricSpace instance: otherwise CompleteSpace resolves the old uniformity
despite the local auxiliary EMetricSpace, producing an instance diamond.
Extendible-ray uniqueness and uniform common-arm identification remain later
obligations; this file does not claim either.
