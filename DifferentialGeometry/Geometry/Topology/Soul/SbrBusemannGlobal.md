# SbrBusemannGlobal.lean

Verified 2026-09-08 in the dev checkout. The specified proper bounded-below single-ray Busemann function produces actual surjective one-Lipschitz maps between all levels above its attained minimum. The actual maps satisfy identity, composition and outer-truncation independence, with no supplied compatibility family.

Empty focused output: 27.7s. Lint-clean named build: 29.9s.
Fresh external public axiom audit: 17s; all 13 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrBusemannGlobal-result1.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

2026-09-08 parent continuation. Shared claim
`b01049f6-5062-481a-923a-4fd05485bd00` also covers SbrRetractionShift and
SbrBusemannDiameter. Source-written, unverified; the actual ascent and
retraction dependency chain must be checked first.

The book targets are thm:sbr-surjective-busemann-level-map and
cor:sbr-busemann-level-map-coherence, master05a.tex:8256-8374. Properness
and boundedness below of the specified single-ray Busemann function stay
explicit. SbrBusemannData supplies compactness and the attained actual
infimum; nonnegative sectional curvature supplies concavity of d-b.

busemannSharafutdinovMap is the actual existing retraction for d-b at
level d-a. It is an ambient total function, with specifications restricted
to b(x)<=d and b_min<=a<=d. Its value has Busemann level min(b(x),a).
The actual metric-level subtype map is obtained by restriction, with no
new existence or compatibility assumptions.

Constant-shift invariance proves independence of the outer cutoff on the
smaller sublevel. The semigroup law inside the larger cutoff then proves
composition, including equality of levels. Surjectivity uses the existing
reversed-coray producer, not just the image of the whole sublevel.

This file and its upstream unverified sources must pass empty focused,
linted named-build and fresh public axiom checks before any Ch8 global
endpoint is claimed complete. Markdown notes remain local under the
user's new ignore rule unless they were already tracked.

Source-only review corrected the translated maximum inequality to
`add_le_add h le_rfl`, preserving the right-side shift. Still unverified.
