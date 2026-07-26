# StepBTransitionOverlap status

## 2026-07-18 canonical framed source repair

The four adapters now use the same framed contract as the live item-3/radius
producers: `expRadiusGp` balls, source map `framedExpDiffeo`, target image
`framedExpMap`, inverse chart `framedChartAt`, and the framed
`normalTransition` compatibility alias at instance-packaging public
boundaries.  `normalOverlap_of_map` constructs the framed overlap predicate;
`normalTrans_mapsTo`, `NormalOverlapOn.decode`, and
`NormalOverlapOn.cancel` use the framed partial-diffeomorphism inverse laws.
The private helper `mem_framed_src` has a fully framed statement.  Its two raw
lemmas are the intentional proof kernel after unfolding `framedExp_source`:
there is currently no public theorem taking `‖z‖ < expRadiusGp` directly to
`z ∈ framedExpDiffeo.source`.  No competing public wrapper is introduced here.

After the canonical dependency chain was refreshed in order, official focused
verification passed against the live framed `NormalOverlapOn` interface.  The
earlier stale raw-versus-framed diagnostics are resolved.  The temporary
private diagnostic predicate used before refresh was removed and is not part
of the source.

Accounting: the overlap source repair and verification are 100% complete.
With `StepBTransition`, this is 2/29 audited migration files repaired and
verified; it does not advance the 0% textbook B1 theorem or the 0%
unconditional endpoint theorem.  Dedicated transition machinery in these two
files is 100%; whole-HCG machinery remains about 60%.

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
