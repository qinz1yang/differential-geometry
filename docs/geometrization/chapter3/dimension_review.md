# Independent source and interface review of AC38–AC40

This review concerns the metric dimension argument in blueprint master207A.tex,
lines 4075–4225, not the curvature, chart, or comparison producers feeding it.
The complete displayed AC38–AC40 proofs and AC41's assembly were read alongside
reference_checks_revision70.md and the relevant AC04/AC08 quantitative-net
contracts. Source and mathematical-interface findings are recorded below;
implementation-specific review and verification are recorded separately when
the corresponding files are stable.

## What the argument may honestly conclude

An already supplied pointed limit is kept fixed throughout. Actual uniform
polynomial covering estimates on source balls imply polynomial covering
estimates on each target ball, zero s-dimensional Hausdorff measure for every
s above the exponent, and the Hausdorff-dimension upper bound on that same
target. The proof does not require target curvature, a target dimension bound,
noncollapse, exact dimension identification, or an additional extraction.

The natural general input order is:

    fixed n ≥ 0;
    ∀ S>0, ∃ C_S>0, ∀ η with 0<η≤1, eventually in source index i,
      an internal η-net of closedBall(p_i,S) has card ≤ C_S * η^(-n).

The constant is fixed before the accuracy and source index. The eventual
threshold may depend on S and η. There is no common tail for every scale.
PointedGHConverges supplies the independently quantified approximation maps;
their eventual condition must be intersected with the net condition after
choosing radius and accuracy. Any supplied subsequence must transport both
conditions along that same strictly increasing index map.

For this general contract, source nets at radius R+1 and mesh δ/4 yield target
nets with coefficient 4^n C_(R+1). Source completeness, properness, and the
length property play no role in this dimension step. The existing convergence
interface already includes target completeness, but the dimension argument
does not use compactness or geodesics to transfer the nets.

## Exact AC38 domain and cardinality checks

The source map has domain the actual closed ball of radius R+2. For
ε<min(1/4,δ/8), a target point of radius at most R has an actual coverage
preimage of source radius <R+2ε<R+1. A source δ/4-net in that latter ball
therefore approximates it. Its center lies in the map's domain, and the image
distance from the original target point is <δ/4+2ε<δ/2.

These image centers need not be in the target ball. One must discard empty
intersections of their open δ/2-balls with the target closed R-ball and select
one point from each remaining intersection. The resulting internal centers
cover at strict distance <δ. Their cardinality is at most the source cardinality,
even if selected points coincide. Continuity, compactness, minimizing paths,
and attainment of a distance infimum are unnecessary.

## Exact ceiling specialization and AC40's constant

The blueprint's AC04/AC08 bound is

    N(n,L,S,η) = (1 + ceil(B_S/η))^n,
    B_S = 4 L² sqrt(n) sinh(2S).

At S=R+1 and η=δ/4, its numerator becomes

    A_R = 4 B_(R+1) = 16 L² sqrt(n) sinh(2(R+1)).

For 0<δ≤1 and A_R≥0,

    (1 + ceil(A_R/δ))^n
      ≤ (2 + A_R/δ)^n
      ≤ (2 + A_R)^n * δ^(-n).

This gives precisely the printed coefficient C_R=(2+A_R)^n. It is preferable
to specialize the ceiling bound before converting to a polynomial estimate:
first converting the source coefficient to (2+B_S)^n and then multiplying by
4^n gives the valid but larger (8+A_R)^n. Such an alternative must not be
reported as the literal displayed C_R.

Natural ceiling requires a nonnegative argument in the usual estimate
ceil(u)≤u+1. Here δ>0 and A_R≥0 supply it. Integer exponent n=0 is legitimate
for the algebraic specialization, with coefficient one and no 0^0 problem
in the Hausdorff-measure proof: all tested measure exponents satisfy s>n≥0.
The geometric AC04/AC08 producer still has its separate n≥1 and L≥1 hypotheses.
Extending the algebraic consumer to n=0 does not prove that geometric producer.

For the original growing-region application, c_i≤1, r_i>8(R+1), the uniform
chart-distortion constant L(n), and the actual source net must all be supplied
on a sufficiently late index. None follows from metric convergence alone.
Chart radii may vary without a positive uniform lower bound.

## Hausdorff conventions and library reuse

The archived BBI text at printed 19–20/PDF 34–35 and printed 22–23/PDF 37–38
was freshly text-extracted and read. Definition 1.7.7 uses finite or countable
diameter-power covers, strict diameter cutoffs, and a positive normalization
constant depending on the exponent. It assigns zero measure to the empty set.
The discussion on printed page 20 uses the restricted metric on subsets and
allows external covering sets. Proposition 1.7.8 gives countable subadditivity;
Definition 1.7.17/Proposition 1.7.19 give the dimension and countable-union
conventions. The exponent reversal at the end of the printed proof of
Theorem 1.7.16 remains the previously recorded project observation; this
implementation route should use positive s−n directly rather than that line.

The retained July 6, 2024 errata page 1 was also freshly text-extracted and
read. It corrects finite-net and dimensional notation in this source region.
Revision70's bounded Chapter10/source-comparison checks are reused unchanged;
no fresh remote errata retrieval or full Alexandrov-source audit is claimed.
The source hashes remain:

- BBI2001: 4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971.
- Retained errata: 68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e.

Pinned Mathlib defines hausdorffMeasure using the gauge ediam^s, with no
additional positive normalization factor. Its measure values should not be
asserted equal to every normalized BBI value; zero-measure statements and
dimension are unaffected by such a factor. The actual available tools include:

- Hausdorff.lean:563, hausdorffMeasure_le_liminf_sum: varying finite covers
  with diameter bounds tending to zero bound the measure by the liminf of
  their total diameter-power weights. Non-strict diameter bounds are sufficient;
  this is an alternative verified interface to strict cutoff contents.
- Hausdorff.lean:824, Isometry.hausdorffMeasure_image: transports restricted
  subtype measure to the ambient image. Its exponent condition is nonnegativity
  or surjectivity; s>n≥0 supplies nonnegativity here.
- HausdorffDimension.lean:188, dimH_iUnion: countable unions have dimension
  the supremum of their dimensions. Ambient balls of positive integer radii
  exhaust a finite-distance pointed space. Their coefficients need not be
  uniform in the radius.

No compactness, measurability of each covered subset, or positive critical
dimensional measure should be silently added. Mathlib's measure evaluates
arbitrary sets through its outer measure; Borel-space structure on an ambient
carrier can be installed canonically when needed. The dimension definition
already uses the canonical Borel structure.

## Boundary retained

This work can discharge AC38, AC39, and the quantitative-net-to-dimension part
of AC40. It does not discharge the actual curvature-to-chart-to-polynomial-net
producer, AC37's nonnegative comparison, or the complete Alexandrov conclusion
of AC41/MC18. No opaque predicate carrying those conclusions should replace
these remaining producers. Riemannian metric and smooth compactness bindings
continue to await their concrete inherited foundation interfaces.

## NetTransfer implementation review

Independently read the complete stable NetTransfer.lean. Its two public
declarations are Metric.exists_internal_finset_net_of_finite_centers and
GC.MetricGeometry.PointedBallApprox.exists_internal_finset_net. The first
accepts external centers indexed by any finite set and returns an internal
strict 2η-net without increasing cardinality. The second applies this to
the exact AC38 closed-ball radii and errors and returns an internal strict
δ-net with cardinality at most the supplied source finite set's cardinality.
An additional bound by N is obtained by ordinary transitivity.

The generic proof filters precisely the centers whose open η-ball meets
the set, then chooses from those nonempty intersections. This handles empty
sets and duplicate selected points: the resulting finite image has cardinality
at most the index set. The geometric proof uses actual coverage preimages,
the basepoint-derived radial bound, and distortion on both source-domain
points. Every source net center is shown to lie in the radius R+2 domain.
Neither continuity nor compactness is used. The weak input mesh inequality
≤δ/4 still gives the asserted strict output inequality because coverage and
distortion are strict and ε<δ/8. No mathematical defect was found.

Independent verification at Lean 4.35.0-rc3 / Mathlib
c55e6e786f49471c72fbddbec5415808896aec1e:

- Targeted build succeeded (1,248 jobs), with no warning in the returned output.
- Both public declarations' axiom closures were checked independently and are
  exactly propext, Classical.choice, and Quot.sound.
- Reviewed source SHA256:
  766bf1e0c5dbafe8e499d55ea7d01340b7debf8ab53fc9c37ba5ec0f06167fd8.

## CoveringLimit implementation review

Independently read all of CoveringLimit.lean, including its private ceiling
estimate. The three public PointedGHConverges declarations return nets on
the existing carrier Y and basepoint q. They intersect the actual eventual
approximation and eventual source-net conditions and choose one index only
after fixing R and δ. Their choice ε=min(1/8,δ/16) has the required strict
error margins. No global index uniform over all scales is introduced.

The first theorem preserves an arbitrary real cardinality bound K. The
polynomial theorem fixes C and a real exponent d before all meshes η, then
returns coefficient C*4^d. Nonnegativity of d is not needed for this algebraic
transfer; the Hausdorff consumer explicitly supplies it. The ceiling theorem
uses a natural exponent n and B≥0 to return exactly (2+4B)^n. The auxiliary
ceiling inequality checks the nonnegative argument and uses δ≤1 before
raising to n. Thus the sharper blueprint constant is retained, including
the cases n=0 and B=0. No mathematical defect was found.

Independent targeted build succeeded (2,050 jobs). All three public axiom
closures were checked and are exactly propext, Classical.choice, and
Quot.sound. Reviewed source SHA256:
ae63f76a2af574456b377e4481fdad501fcca7139388ab6a967fbd51c8802969.

## PolynomialCovering implementation review

Independently read the complete main estimate and all eight public corollaries
in PolynomialCovering.lean. The primary result allows any set A in a metric
space, a real exponent n≥0, and a fixed positive real C. Its net-size bound
holds at every mesh 0<δ≤1; neither compactness nor a measurability assumption
on A occurs. Internal ambient finite sets and finite sets of the restricted
subtype both have public interfaces.

The proof takes δ_k=1/(k+1), covers by intersections with closed δ_k-balls,
and bounds the extended diameters by 2δ_k. The sums of s-th powers of these
diameters are bounded by C*2^s*δ_k^(s-n). Here s>n≥0 ensures both that
raising diameter inequalities preserves them and that the upper bounds
converge to zero. Mathlib's actual Hausdorff-measure liminf theorem then
proves measure zero. This also handles empty sets and n=0; no critical
exponent claim or 0^0 convention is needed. The dimension proof uses
Mathlib's actual dimension definition and excludes infinite s-dimensional
measure above n.

The subtype adapters use the inclusion isometry; they do not assert an
unproved equality of intrinsic path distances with restricted distances.
Countable-union measure vanishing is proved both from separate polynomial
bounds and directly from restricted-subtype measure zero. The latter is
the literal additional AC39 assertion and needs only s≥0. Constants may
depend on the union index. The union dimension proof uses Mathlib's
countable-union dimension theorem. No mathematical defect was found.

Independent targeted build succeeded (2,622 jobs), and all nine public
declarations' axiom closures were checked and are exactly propext,
Classical.choice, and Quot.sound. Reviewed source SHA256:
ec8be7807bbc24806d7b48272ad1ba5f0bd515fc8a8ba43bee2a220bfa1f2775.

## DimensionLimit implementation review

Independently read the initial stable DimensionLimit.lean and its four public
declarations. The supplied-limit measure and dimension theorems keep the
same Y, metric, q, and PointedGHConverges proof. Their source input order is
exactly: for each R>0, one positive real C; then every mesh 0<η≤1; then an
eventual actual internal source η-net with size at most C*η^(-d). The global
exponent is a fixed nonnegative real. Neither target curvature nor a target
dimension bound appears among the hypotheses.

The private ball consumer uses source radius R+1 and coefficient C*4^d;
positive integer-radius closed balls exhaust Y because the metric distances
are finite. Their constants can vary with the integer radius. The supplied
limit consequently has zero s-dimensional measure for every s>d and dimension
at most d. The measure statement explicitly uses a Borel measurable structure;
the dimension statement needs no such extra instance.

The extraction theorem first converts these actual covering estimates to
MC13's uniform eventual finite-cardinality nets. For arbitrary η>0 it uses
min(η,1), so no large-mesh case is dropped, and rounds up the finite real
bound with Nat.ceil. It invokes the existing MC13 constructor once. The
polynomial source estimates are then transported along that exact strictly
increasing subsequence using convergence to atTop. Applying the already
reviewed supplied-limit dimension theorem therefore adds dimension to the
same carrier, metric, basepoint, and subsequence; no replacement limit or
implicit uniqueness argument is used.

The optional geodesic theorem additionally requires actual continuous curves
of Mathlib variation less than dist(a,b)+ε, for every source, endpoint pair,
and positive ε. It applies the existing midpoint/segment consumer to the
same extracted proper limit and the curves along the same subsequence. It
does not assume source completeness, properness, geodesics, or curvature.
Target completeness remains inside PointedGHConverges, and properness is
constructed by MC13. No mathematical defect was found.

Independent targeted build succeeded (2,656 jobs); all four public axiom
closures are exactly propext, Classical.choice, and Quot.sound. Reviewed
initial source SHA256:
882ff54ee37ed2f5d67cf9ee6176d5e3e430b635b0585b715868e3e0da1d3c56.
The exact one-ball ceiling constant is already checked in CoveringLimit.
Any later family-wide ceiling adapter requires its own addendum; this review
does not silently treat it as part of the present four declarations.

During this review the workspace's physical location moved under
Documents/Documents - Unknown. The DimensionLimit checks above ran in the
same checkout at that new location. No Lean source, prior checkout, reference
archive, configuration, or git state was modified by this reviewer.

## Final ceiling-family addendum

Independently read the added private
polynomial_nets_closedBall_of_ceil_covering helper and the public
PointedGHConverges.hausdorffMeasure_univ_zero_of_ceil_covering and
PointedGHConverges.dimH_le_of_ceil_covering declarations. They fix a natural
exponent n and one real-valued function B before all source radii, meshes,
and indices. For each R>0 and 0<η≤1, an eventual actual internal source net
is assumed with cardinality at most (1+ceil(B(R)/η))^n. The only additional
condition on B is nonnegativity at positive radii; continuity, monotonicity,
or a uniform positive lower bound is not imposed.

Here B is the source ceiling numerator. For the blueprint application,
B(S)=4*L^2*sqrt(n)*sinh(2S), whereas its target numerator A_R is
4*B(R+1)=16*L^2*sqrt(n)*sinh(2(R+1)). These two normalizations are distinct.
The helper applies the exact CoveringLimit theorem at source radius R+1
and mesh δ/4, giving precisely (2+4*B(R+1))^n*δ^(-n). It does not
polynomialize the source estimate first and therefore does not substitute
the larger coefficient (8+4*B(R+1))^n.

For the global countable union, target radius i+1 correctly uses source
radius i+2. Nonnegativity of B there makes the target coefficient positive,
including n=0 and B=0. The same existing pointed limit is used throughout.
The resulting measure statement holds for every real s>n, and the dimension
statement embeds n into Mathlib's extended nonnegative reals. No geometric
producer or assumed target dimension/comparison property is hidden in either
statement. No mathematical defect was found.

The final targeted DimensionLimit build independently succeeded (2,656
jobs). Both added public declarations' axiom closures were checked and are
exactly propext, Classical.choice, and Quot.sound. Final reviewed source
SHA256:
c342b9e1f2dc5a5dc33c3e63674868292720b4f935b0b2fb427aa3515373765a.
Together with the preceding checks, all twenty public declarations in the
four new modules have now been independently reviewed and axiom-checked.
