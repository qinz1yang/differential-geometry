# SbrBusemannLevelMap.lean

Verified 2026-09-08 in the dev checkout. Actual Sharafutdinov maps send a higher Busemann level onto the lower one; reversed corays and proved uniqueness supply every preimage. Compact upper sublevel and nonempty lower level suffice for an actual surjective one-Lipschitz metric-subtype map.

Empty focused output: 19s. Lint-clean named build: 23.8s.
Fresh external public axiom audit: 17.1s; all 3 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrBusemannLevelMap-result2.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

2026-09-08 parent source work. Claim
`6649b3e7-3ef2-4637-b259-57d4fa47b979` retained. Three public theorems,
source-written and unverified. All direct producer leaves must first pass
their own focused checks, named builds and public axiom audits.

This implements the actual surjectivity argument in
thm:sbr-surjective-busemann-level-map-local, master05a.tex:8159-8254.
The inputs are the native complete Riemannian manifold, nonnegative
sectional curvature, one specified isometric ray, a nonempty lower level,
and a compact upper sublevel. No global properness or lower bound is
added to the pairwise theorem.

For the actual complementary function F=c2-b, choose the standing data
produced in SbrBusemannPairData. The produced Sharafutdinov map at
T=c2-c1 sends every upper-level point to the lower level by calibration.
For an arbitrary lower-level point y, SbrCorayAscent produces a reversed
coray from the upper level to y with exact levels and actual normalized
gradient derivatives for times below T. Ascent uniqueness on [0,T]
identifies that coray with the already produced level-map orbit. Its
terminal value therefore proves surjectivity, including T=m. No right
derivative at T and no backwards nonsmooth flow is assumed.

The first theorem proves the exact image of the actual ambient retraction.
The second assembles all geometric inputs and restricts its one-Lipschitz
bound to the upper level. The third returns a surjective one-Lipschitz
function between the actual metric level subtypes. Global proper-exhaustion
assembly, coherent choices across truncations and diameter monotonicity
are later consumers, not implicit inputs to these sources.

This is the kind of level-map producer used by the Ch23 outward-neck
comparison and consequently Ch25's terminal-limit global curvature bound.
It is not a verified Ch8 or downstream endpoint until its whole dependency
chain and its own verification triple pass.
