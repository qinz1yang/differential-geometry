# AC13: actual open-ball finiteness and local metric equality

Six public theorems in two leaves prove finiteness and local agreement for
the actual intrinsicEDist constructed from all paths in the ball subtype.
The ambient metric space has only the explicit length-curve property.
Ambient completeness, local compactness, geodesicity and curvature are NOT
assumptions in these conclusions.

Variation comparison works across different target metric spaces whenever
their pairwise edistances on the parameter set are ordered or equal.
Isometries preserve actual variation. A controlled ambient curve lifts to
the region subtype with the same variation, giving an intrinsic upper bound.

For L>0, intrinsicEDist is finite between every pair of points in B(o,L).
For each endpoint, a path from o with length<L remains in the ball; reversing
one such path and concatenating gives finite intrinsic distance. This is
actual finiteness, not an additional input to the metric constructor.

For h>0 and d(x,o)+4h<L, points a,b in B(o,L) whose ambient distances to x
are at most h satisfy intrinsicEDist(a,b)=edist_X(a,b). Given any positive
error epsilon, the proof takes an almost-shortest ambient curve with error
min(epsilon,h/2). Triangle estimates keep its entire range in B(o,L).
The exact lifted variation bounds the intrinsic distance, and letting the
error decrease proves equality. This includes endpoints on the closed
inner ball and coincident endpoints. No convexity or path-minimizing
property of either ball is assumed.

Sources actually used: frozen blueprint207A AC13 full2713-2755, especially
the complete finiteness and4h local-identification arguments. BBI2.1-2.3
and the retained July6,2024 errata reading from intrinsic_edist_sources.json
are reused unchanged. Mathlib BoundedVariation.lean54-95 actual partition
supremum and accepted IntrinsicEDist/PathVariation bodies were reread.
Exact source hashes and locator records are retained separately.

The induced finite metric is now available on an open ball by the preceding
constructor and this finiteness theorem. Equality of generated/original
topologies, complete common balls and the induced length property still
require proof. Thus full AC13 and full ALG06 are not claimed. Earlier math
leaves and blueprint207 remain unchanged; no PC interface is altered.
