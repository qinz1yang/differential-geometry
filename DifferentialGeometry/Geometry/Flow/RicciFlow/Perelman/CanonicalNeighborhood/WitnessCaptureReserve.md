# WitnessCaptureReserve

Chapter25 task; claim4639c87c-17e5-4cbd-bb79-67ca9833316b.
ACCEPTED 2026-09-10: saved check1 EMPTY (26.4s), named lint build1 (53.5s),
fresh WitnessOpennessPartsAxioms1 verifies both publics standard-only.

Book lem:scn-model-witness-stability, openness requires source capture to
survive perturbation. First prove that every actual witness has spare capture
radius, without relying on its existing source_capture field. The comparison
(1-eps) h <= F* g captures radius sqrt(1-eps)/sqrt(eps). For every 0<eps<1
this strictly exceeds 1/sqrt(eps)-1, so the same image contains a CLOSED
source ball of radius 1/sqrt(eps)-1+eta for some eta>0.

The argument reuses CrossModelBallCapture's proved first-exit lemma with the
actual model ball, original embedding and actual normalized source metric.
Ancient-model completeness supplies compactness. This proves a strict reserve
at the old witness; transporting the finite comparison under recentering and
moving source time is still necessary for openness.

Receipts: E:/lean-tools/chapter25-book-20260910/. Current compiler/claim
ownership is recorded only in WORKING_STATUS.md.
