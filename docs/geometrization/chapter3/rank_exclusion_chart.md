# AC27: an actual chart from exclusion of the next rank

Four public theorems prove the lower coordinate bound, produce the actual
open-image bilipschitz homeomorphism, and give the direct Hausdorff ceiling
for a pointwise packet. The generic metric helper constructs a homeomorphism
onto the actual range from upper/lower Lipschitz bounds, retaining the map
pointwise and proving the inverse constant.

`PairedComparisonPacket.exists_chart_of_rank_exclusion` uses the same packet,
common domain, original anchors, distance bounds, almost-short curves and
local complete closed balls as AC23/26. Its precise quality assumptions are
0<beta<=1/(200(m+1)) and 0<delta<=beta/100. It assumes no quality-beta packet
of rank m+1 centered in V with all anchors in Omega, expressed using arbitrary
Option-indexed anchor families. With r>0, B(q,3r) contained in V and
2r<=min(1,a0/2,epsilon/K), it returns an OPEN U and an actual homeomorphism
B(q,r) to U, whose values equal the original Euclidean distance coordinates.
Its lower constant is epsilon=(beta/(100*pi))^2, upper constant sqrt(m), and
inverse constant epsilon^(-1). No change of metric or anchors is made.

The exclusion is used to force at least one coordinate difference above
epsilon*d(x,y); PiLp coordinate evaluation gives the Euclidean lower bound.
Openness follows by restricting the existing uniform packet to the open ball
and applying the already proved geometric open-map theorem. This avoids
repeating pointwise localization with doubled quality. The restricted ball is
not assumed to be a length space. V itself need not be open once the 3r
buffer is supplied. The general lower-bound theorem allows empty old index;
the chart theorem requires positive finite rank.

`PairedComparisonPacket.card_le_dimH` applies pointwise AC23 with doubled
quality and proves card(iota)<=dimH(Omega), under 0<beta<=1/(200*card(iota)).
The centers have a genuine neighborhood inside the same comparison domain;
anchors are required to lie in that domain. The rank ceiling is not a claim
that every neighborhood already contains a maximal-rank packet or a chart.
AC28's finite hierarchy, transport/local compactness and curvature-to-covering
production remain open.

The full AC27 blueprint207A statement/proof (lines3404–3438), AC28's intended
consumer, and revision66 source comparison were reread. Unchanged BBI/BGP
and author-errata checks are reused from angle_reversal_midpoint_sources.json.
The homeomorphism construction uses the pinned Mathlib embedding-to-range
API, inspected in full for its actual map and inverse. Earlier mathematical
leaves, frozen207 and the PC/Riemannian migration interface remain unchanged.
