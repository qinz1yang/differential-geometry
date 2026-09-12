# SbrRetractionShift.lean

Verified 2026-09-08 in the dev checkout. Actual Sharafutdinov retractions are invariant under adding the same nonnegative constant to the function and target level on the original domain. Actual gradient equality and time-shifted uniqueness prove the comparison through the terminal level.

Empty focused output: 18.5s. Lint-clean named build: 23.5s.
Fresh external public axiom audit: 17.4s; all 1 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrRetractionShift-result4.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

2026-09-08 parent continuation. Claim
`b01049f6-5062-481a-923a-4fd05485bd00` is shared with the new
SbrBusemannGlobal and SbrBusemannDiameter leaves. Retain it until all three
files are edited and verified. SOURCE-ONLY during Chapter23's current
compiler window; no verification of this leaf has run.

The actual retractions for F and F+k agree after shifting the level by k,
on the original nonnegative set, for k>=0. Both compact nonnegative sets
and both attained global maxima are explicit data of the existing
construction. Gradient equality is the proved SbrGradientShift identity,
not a new assumption. The time-shifted orbit has the same native right
manifold derivative, level and initial point; SbrFlowUniqueness identifies
the two curves on the closed interval through the requested level.

This is the outer-truncation comparison needed by the book's
cor:sbr-busemann-level-map-coherence. It includes the maximum level by
continuity, and treats already-fixed points directly. No inverse flow or
compatibility of selected Euler limits is assumed.

Source review before the next compiler window: use `add_le_add h le_rfl`
for adding the same constant on the right; the current native generated
`add_le_add_right` adds on the left. The derivative composition now
specifies its actual affine inner function explicitly. These repairs are
not yet compiler checked.
