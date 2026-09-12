# Chapter25FiniteHorn

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
Scope: full Chapter25 skeleton; earlier integration deferred by the user.
Current review (2026-09-09): D1 added open embedding, positive artificial-frontier
distance and punctured-neighbourhood capture. This excludes the OLD height-zero
product example discussed below; those historical paragraphs no longer describe
the current signature. No current full EndGeometry proof follows from that exclusion.

The remaining ambient issue is metric length provenance. CompleteSpace and local
distance agreement do not imply that ambient distances are infima of curve lengths.
A concrete mathematical test is the small-angle round cone
`(0,1) x S^2`, `dr^2 + a^2 r^2 g_S2`, completed at both ends. In its ambient metric,
allow extra positive-cost jumps between pairs on levels `r_n -> 0`, each of cost
one half their old distance, and take the infimum of these chains and ordinary
segments. The new metric lies between one half and one times the old metric,
so it has the same topology and is complete. The radial coordinate is still
1-Lipschitz and distances to the vertex still equal r. The jumps accumulate only
at the vertex, so the inclusion is locally isometric at every horn point, open,
and has punctured-ball capture and outer-frontier distance one. But pairs on the
jump levels have strictly shorter ambient distances at arbitrarily small radii.
The intrinsic horn and its fixed-precision neck data are unchanged. This is a
mathematical counterexample test, not a Lean-checked construction of the full record.

Thus `EndGeometry.intrinsic_ambient` still needs an ambient length-space / actual
source metric argument. Do not replace it by an assumed distance-equality field.
Use the actual positive frontier-distance constant d0 in rescaled estimates;
`cut_height` is a topological product coordinate and cannot be substituted for d0.
The seven-card expansion remains frozen under the current plan's D1 decision.

The frontier field can be pursued separately from full distance equality:
local_distance plus the INTRINSIC length definition of W should first give
`dist (inclusion x) (inclusion y) <= dist x y`. Taking y along the axial ray to
the missing end then gives `dist (inclusion x) ambient_end <= r_E(x)`.
Consequently frontier_far gives `dist (inclusion x) z >= d0 - r_E(x)`, which
already suffices for frontier_escape. This upper-distance route needs no
ambient length assumption; the latter is needed for the reverse comparison in
intrinsic_ambient. The global nonexpansion lemma is not yet implemented here.

Current seven-card consumer audit (proof routes, not newly verified proofs):

| Card | Actual next consumer | Route / unresolved data |
|---|---|---|
| END-RAYS | Ray approximation, end angles, smooth cone patch | Earlier intrinsic endpoint/ray proofs cover two fields. Ambient length provenance is still missing for intrinsic_ambient. Frontier escape can instead use global nonexpansion and frontier_far, as above. |
| END-RAY-APPROXIMATION | END-ANGLE | Use a common axial base, whole minimizing arms, all cross-connectors and terminal truncation. The written fixed-W depth threshold does not close the card for arbitrary positive collar_depth; obtain a usable uniform collar from the actual construction before wiring it. |
| END-ANGLE | Direction compactness, cone convergence, two-scale comparison | Local comparison on every required minimizing lens gives shortening monotonicity; bounded monotone angles have a two-parameter limit. Prove its triangle inequality and use the genuine zero-distance quotient. A chord-distance triangle inequality alone is not yet the angular triangle inequality. |
| DIRECTION-COMPACTNESS | Cone convergence and upper two-scale bound | For each finite separated family choose one common base close enough to E, compare all its initial unit vectors, and use a dimension-three sphere packing bound. For nontriviality combine deep ray coverage with geodesic uniqueness: zero angle identifies equal-radius points on sufficiently short rays, so a three-dimensional open end cannot have just one ray germ. Neither part is presently wired. |
| CONE-CONVERGENCE | Two-scale comparison and smooth cone patch | Finite angular nets and radial sampling must approximate both entire compact annuli, including completed directions. Eventual radii must fit every chosen finite representative; ray coverage handles the W-side surjectivity. Keep the marked reference ray and radial function. |
| TWO-SCALE-COMPARISON | Smooth cone patch | The positive lower bound comes from curvature_distance_lower on a deep tail. An unbounded upper subsequence gives HornBarriers with sphere diameter o(r_E). A second positive-angle ray crosses from (1-eta)r_E to (1+eta)r_E while staying distance comparable to r_E from the reference ray, contradicting the global barrier. Constructing those radial barriers remains the substantive missing step. |
| SMOOTH-CONE-PATCH | finite_horn_produces_cone, then the proved cone_terminal_exclusion | Diagonalize source maps on each fixed curvature-scale compact before letting it move. Retain the source basepoint, actual scalar normalization, map-composition identity and identification with the annular metric cone. ConeFlowLimit currently does not store these relations to RealizedFiniteHorn; the three new ambient fields do not provide them. |

This audit does not unfreeze the family: END-RAYS and the uniform collar/source
provenance gates remain unresolved. The immediate executable work is the separate
normalization and shared terminal-slab review follow-up.

Status: original cone_terminal_exclusion is proved and standard-only; ten
finite-horn/distance proof obligations remain. The fixed-precision/full-arm
and deep-cutoff corrections are verified.
Neck-side repair verified on 2026-09-09: side focused4 passed43.96s at
SHA1C877A66; parent named3 passed44.23s/11519 with only existing placeholders.
Fresh18-public NeckRepair audit1 passed23.39s: all six new geometric helpers
and the original cone endpoint are standard-only; the other11 remain conditional.
Side claim e4379035 and parent integration claim5d09005a are released.
Current-interface downstream checks/builds/audits are complete; see section4
of CANONICAL_NEIGHBORHOOD_PLAN.md and the early return in WORKING_STATUS.md.
Mathematical obligations remain, including producing the added tube data.
Claim81632958-ad9f-4ca5-be37-f132e6ef0f79 was released after commit6f07c2d242;
release/handback is recorded in WORKING_STATUS.md.

Original cone closure: focused3 passed (40.33s), named2 passed (55.45s/11519),
fresh12-public audit2 (30.78s). Exactly ten original placeholder warnings;
cone_terminal_exclusion alone in this original leaf is now standard-only.
Original public theorems: 12; new neck helper theorems: 6;
explicit own obligations: 10; earlier obligations: 0.
Current receipts: E:/lean-tools/chapter25-terminal-local-20260909/.
Historical skeleton receipts remain under chapter25-skeleton-20260908/.

The seven cards remain own Chapter25 proof obligations. Distinguish intrinsic and ambient completion, and the raw ray family from its zero-angle metric quotient. Annular correspondences must cover both full annuli. Cone smoothness uses the actual source limit embeddings. The local cone exclusion does not assume source convergence. In mixed bounded quantifiers write forall i, forall s in S; explicitly type EndRay arguments of comparison-angle monotonicity.

2026-09-09 consultation correction: approximation is asserted below a positive common deep cutoff; pairwise angle monotonicity has a positive local cutoff. Arbitrary outer ray extensions are not controlled by deep-end geometry. Full arms and all cross-connectors are retained. EndRayLocality supplies the short-representative and zero-angle consequences. No known downstream invocation used the old arbitrary-length signatures. The raw ambient frontier-escape defect remains explicit and is not repaired by the cutoff alone.

Reproduce with the shared E:/testdifferential-geometry/scripts/lake-locked.ps1
from the dev cwd, serial one-thread focused/named checks in an explicitly granted
exclusive window. Do not reuse the failed/intermediate receipts. The current
coverage and proof accounting are in CANONICAL_NEIGHBORHOOD_PLAN.md section9.

The horn constructor now chooses admissible precision/depth ranges before its
source tolerance and returns the requested fixed values. No arbitrary-accuracy
tail claim on the same horn survives. Ray connectors cover full radial arms.
Barrier diameter control is eventual: hlarge only forces positive source
curvature eventually, so an all-index inverse-sqrt bound can fail at an initial
zero-curvature point. The actual global tube, its ordered cross-sections and
radial control still need to be returned by the geometric construction; the
current local-distance/subend fields alone do not discharge those obligations.

Concrete obstruction: ambient = Completion W x Real and inclusion(x)=(x,0)
satisfy the recorded ambient fields, but the whole image belongs to its
frontier. The proposed frontier_escape then fails on axial sequences. The
end-rays signature is documented as awaiting actual ambient/global tube
provenance; do not try to fill this sorry from the current raw record.

Verified 2026-09-09, source8f59c3f28: focused 27.1s (only the original explicit-placeholder warnings); named lint build 37.5s; fresh107-name audit. The existing own obligations and conditional endpoints remain.
Exact hashes/logs: E:/lean-tools/chapter25-cone-chart-20260908/completion.json.
Current ownership/claim state is in WORKING_STATUS.md.

2026-09-09 neck interface repair, side task01a08501-1988-7dc2-8cbe-d7dcaeb73c2a:
FiniteHorn now requires an actual global smooth product tube and cofinal product
subends. Every chosen tail collar returns a GlobalNeckCrossSection witness:
the SAME central sphere extends to a global product presentation, a whole deep
subend lies on its lower side, and the actual finite axis meets the sphere.
Six new geometric theorems derive continuous height, its range, full section
membership, compact closed slabs and global path separation from these maps.
RayApproximation now retains three common buffers with closure containment,
smooth WHOLE arms and smooth WHOLE connectors contained in the recorded buffers.
The constructor must produce these data; no seven-card conclusion is stored as
a new hypothesis. The ten original own proof obligations remain unfilled.

The new cylindrical_tail conjunct is immediately after the center equality:
Nonempty (GlobalNeckCrossSection F subend axial.point axial.length).
Consumers destructuring the old tuple must retain/skip this additional witness.
This is a source/API repair, not completion of the gluing constructor or radial
barrier estimates. In particular the arbitrary ambient Completion W x Real
counterexample STILL applies to the separate raw ambient fields. Openness,
compact slabs and global topological separation do not establish source capture
or intrinsic=ambient distance; finite_horn_end_rays must not be counted proved.
Focused/audit records for this repair: E:/lean-tools/chapter25-neck-side-20260909/.
Final focused4 passed in43.96s with only the ten original sorry warnings;
no new warnings or errors. Frozen source SHA256:
1C877A66C25A1B65C937D91338BE16751154AC4181D5A75578EAB259CACCB77C.
The main task owns the exclusive artifact window and will perform the named
refresh, downstream tuple adaptation check and fresh NeckRepairAxioms.lean
audit. This side has not yet verified those stages. No original slot was closed.

Deep-cutoff correction verified 2026-09-09: focused1 (38.37s) has only the
original11 placeholder warnings, named1 passed (52.27s), fresh12-public audit1
retains sorryAx in every original endpoint. Receipts:
E:/lean-tools/chapter25-terminal-local-20260909/.
This repairs overstrong quantifiers; it does not close a finite-horn card.
