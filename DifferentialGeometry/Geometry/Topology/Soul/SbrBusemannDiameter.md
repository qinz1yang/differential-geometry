# SbrBusemannDiameter.lean

Verified 2026-09-08 in the dev checkout. Actual Busemann level diameters are finite and monotone above the attained minimum, using the produced surjective one-Lipschitz maps. The compact-sublevel pairwise version also avoids global properness and boundedness-below assumptions.

Empty focused output: 19.3s. Lint-clean named build: 22s.
Fresh external public axiom audit: 17.6s; all 4 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrBusemannDiameter-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

2026-09-08 parent continuation. Shared claim
`b01049f6-5062-481a-923a-4fd05485bd00` also covers SbrRetractionShift and
SbrBusemannGlobal. Source-written, unverified; no compiler or audit has
run for this leaf or its pending actual flow/map dependencies.

The book target is cor:sbr-busemann-level-diameter. The local version uses
only a nonempty lower level and a compact upper sublevel. Compactness of
both levels follows by closedness. The actual surjective nonexpanding
level map lifts each pair of lower-level points to upper-level points,
so the lower diameter is bounded by the upper diameter.

The proper-exhaustion version uses the actual named global family from
SbrBusemannGlobal, includes equal levels, and yields MonotoneOn above the
attained minimum. Finiteness is expressed using Metric.ediam < top, so
it is not confused with the total real-valued diameter of an unbounded
set. Properness alone supplies this finiteness for every level.

This is the diameter comparison required by the Ch23 outward-neck
argument. No downstream Ch23/25 source is changed, and no verified
integration into those chapters is claimed.
