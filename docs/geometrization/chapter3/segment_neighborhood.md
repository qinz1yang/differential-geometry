# Segment neighborhoods and the recognition boundary

This layer proves six reusable metric theorems in
`Topology/MetricSpace/SegmentNeighborhood.lean`. It supplies the metric
no-exit arguments of ALR03–ALR04 and the final distance-coordinate step
of ALR02. It does **not** establish AC46 from curvature and dimension.
The producer of local distance-coordinate injectivity remains open.

## Exact statements

For an actual isometric segment sigma:[a,b] -> X and p in [a,b],
assume r <= min(p-a,b-p). If distance from sigma(a) is injective on
the ambient open r-ball at sigma(p), then that ball is exactly
sigma({t in [a,b] : |t-p|<r}). No geodesic, curvature, completeness,
properness or dimension assumption is needed for this implication.
Local injectivity at each segment-interior point consequently makes
the image of the segment interior open in X.

If X has constant-speed minimizing segments between every pair and
the image of (a,b) under sigma is open, the same ball equality holds
for EVERY r <= min(p-a,b-p). This includes equality at the endpoint
distance and nonpositive radii (empty balls). The supplied segment
has its original restricted metric.

For sigma:[0,D] -> X, assume the segment interior is open and p=sigma(0)
is a metric endpoint: whenever d(x,p)+d(p,y)=d(x,y), x=p or y=p.
Then B(p,r)=sigma([0,r)) for every r<=D. D=0 and r<=0 are allowed.
The endpoint hypothesis is the metric betweenness formulation; this
module does not separately prove its equivalence with the blueprint's
no-minimizing-segment-interior wording.

For positive radii the last two conclusions are exported as actual
onto `IsometryEquiv`s from (-r,r) or [0,r) onto the actual ambient
ball subtype. The public conclusion fixes the image of zero to the
given center. These are isometries for restricted ambient distances,
not merely homeomorphisms or intrinsic-length identifications.

## Proof and source comparison

The distance-coordinate argument sets t=a+d(sigma(a),z); the reverse
triangle inequality puts t in the segment and the ball. Injectivity
identifies z with sigma(t).

The no-exit proofs use Mathlib's connected-image theorem and
`IsPreconnected.subset_of_closure_inter_subset`. The segment range is
compact and closed; its open interior contains every point at which
a joining segment can meet it. This replaces the written last-time
maximum with the equivalent connectedness argument. In the endpoint
case choose a=(D-d(p,z))/4. A joining segment from sigma(a) to z
cannot reach sigma(D), by its length, or p, by the endpoint condition.
No nonbranching or space-of-directions theorem is assumed.

The archived AKP *Alexandrov geometry: foundations*, Theorem 15.18,
printed/PDF page 238, was read in full, as was pinned branch vol1,
commit ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245, `dim.tex`
lines 874–951 (label `thm:dim=1.CBB`). Its proof invokes Proposition
15.7 and linear dimension to exclude the third direction. This layer
does not import that argument: openness/injectivity is explicit input.
Blueprint207A ALR02–ALR04 and revision139's source comparison supply
the exact metric decomposition. Source hashes are recorded in
`evidence/segment_neighborhood_sources.json`.

The official author errata PDF was checked externally on September29,
2026; its body is dated July12,2026. Its published-page238 Section J
correction is distinct from the archived-page238 recognition theorem.
The archived repeated direction at the end of the proof remains a
project-observed issue, not an author-issued correction; this argument
does not use directions. No whole-book or dimension-theory audit is claimed.

## Verification and remaining work

The combined manifest gate and a separate declaration-linter/consumer
check are run for this layer; the evidence files record their actual
outcomes. All earlier mathematical leaves and blueprint207 are preserved.
The full migrated PC root is outside this branch's scoped build.

Still needed for general one-dimensional recognition: geometric
production of local distance-coordinate injectivity (the rank exclusion
and paired-chart argument). Complete line/ray/interval/circle classification
AC47 and the other AC48 product models remain separate. This layer is
independent of Ziyang's Riemannian migration and introduces no admissions.
