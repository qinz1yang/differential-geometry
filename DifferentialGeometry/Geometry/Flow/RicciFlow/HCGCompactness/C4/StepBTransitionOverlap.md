# StepBTransitionOverlap status

Status: 2026-07-13, focused verification passed without warnings or `sorry`.

`normalOverlap_of_map` turns source/target C2-radius inclusions plus an
exponential-image containment into the canonical `NormalOverlapOn` predicate.
`normalTrans_mapsTo` produces the coordinate maps-to fact from the same image
containment, and `NormalOverlapOn.cancel` gives the reverse-transition
cancellation on the overlap.  These are compatibility adapters over the
existing normal-coordinate API, not new transition assumptions.

This overlap-adapter sub-brick is 100%.  Stable-pair geometric containment and
the finite transition diagonal remain separate producers.  Dedicated
Step-B/B1 machinery is about 83%, Chapter 4 machinery about 79%, and whole-HCG
machinery about 53%; `StepB1RawInput`, textbook B1, and the conditional
compactness endpoint remain theorem-level 0%.

## 2026-07-15 canonical overlap decoding

Added `NormalOverlapOn.decode`: on a verified normal-coordinate overlap,
decoding a transition in the target chart gives the same manifold point as
decoding the original vector in the source chart.  The proof uses only the
existing overlap predicate and normal-chart inverse law; it adds no transition
wrapper or radius assumption.

Focused verification passed.  This is a reusable lower-layer projection lemma,
not an all-pairs stage-map result.  Current rounded estimates remain about 94%
for dedicated Step-B/B1 machinery, 86% for Chapter 4, and 57% for whole-HCG;
`StepB1RawInput`, textbook B1, and every compactness endpoint remain 0%.
