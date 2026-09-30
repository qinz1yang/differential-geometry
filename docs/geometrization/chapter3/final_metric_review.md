# Independent review of correspondences, scaling, and the MC01 boundary

The full statements and proofs of Correspondence.lean, Scaling/Rescale.lean,
and ScaledProductCollapse.lean were independently reviewed against blueprint
master207A.tex, MC04–MC05 at lines 916–986 and MC16 at lines 1743–1760.
No mathematical defect or contract mismatch was found in these files.
CompactComparison.lean and ProductCollapse.lean were also read to check their
actual upstream estimates. This review makes no whole-chapter completion claim.

## MC04 and MC05

The correspondence formula uses an actual relation onto both nonempty compact
metric spaces and the actual real supremum of all its pairwise distance errors.
Compactness supplies an upper bound; nonempty correspondences supply zero in
the error set. The final infimum is over a nonempty set of distortion values,
bounded below by twice the GH distance. There is no unjustified empty supremum
or unbounded real infimum in the formula.

The half-distortion bound indexes Mathlib's approximate gluing by the whole
relation. Its two coordinate maps need not be injective, continuous, or onto
by themselves to construct the glued metric; the correspondence's surjectivity
is then used for Hausdorff coverage. For distortion bound D, nonemptiness forces
D ≥ 0, and gluing at D/2+δ, δ>0, handles D=0 without identifying points across
the disjoint union prematurely. The proof then removes δ.

The reverse direction uses Mathlib's attained optimal compact coupling and
compact nearest-point attainment. It obtains a relation at the non-strict
threshold dGH, including dGH=0. Thus the stronger assertion of an optimal
correspondence is justified; it does not assume strict witnesses at an infimum.
The existing MetricSpace GHSpace and the isometry-equivalence characterization
of its points supply the blueprint's metric-on-isometry-classes assertion.
This library foundation is reused rather than reproved in Correspondence.

MC05's map converse selects partners in that relation, and its inverse theorem
selects the actual supplied coverage witnesses. All constants agree with the
blueprint: forward GH bound 3ε/2, inverse distortion 3ε, composite errors ε
and 2ε, and converse distortion and coverage 2a. No map continuity is assumed
or concluded. The inverse theorem validly needs neither compactness nor a
positive ε; ε=0 gives the exact estimates. Its empty-space case is vacuous,
with no element of an empty space selected. Compact GH claims retain both
nonemptiness hypotheses. The relation formula's real D is allowed to be
negative, in which case both sides of its bound/existence equivalence are false.

## Positive distance scaling and MC16

MetricSpace.rescale constructs a metric on the original carrier with distance
c times the old distance, for c>0. MetricSpace.ofDistTopology is supplied the
explicit ball comparisons, so the topology is definitionally the old topology.
The identity homeomorphism, forward c-Lipschitz bound, and inverse 1/c bound use
the correct directions. Compactness is transported from compactness in the
original topology; it is not proved without that hypothesis. Boundedness is
equivalent, and the diameter identity is proved for bounded subsets, including
the empty set. No interpretation of real diameter for an unbounded set is used.

ScaledProduct constructs the L² product using Mathlib WithLp 2, with only the
fiber distance scaled by t. Its formula is exactly

    sqrt(dY(y,y')² + t² dF(a,a')²), t>0.

The diameter on the right of the GH estimate is computed with the original
fiber metric. The proved bound is t diam(F)/2, not t² diam(F)/2. Both compact
factors are nonempty for the compact GH theorem. The convergence theorem admits
every positive sequence tending to zero; monotonicity is unnecessary. The
pointed version needs only completeness of the base and compactness of the
fiber, with selected basepoints furnishing nonemptiness. Its approximation is
the actual projection on the actual closed product ball; points (y,q) supply
coverage inside that ball. No metric at t=0 is asserted on the product carrier.

These are distance-metric statements. They do not identify a Riemannian tensor
rescaled by t² with this distance metric, construct flat tori, prove their
dimensions, or provide a fibration theorem. Those illustrative or geometric
adapters must not be counted as consequences merely from the shrinking-factor
estimate. The existing PointedBallApprox.rescale is a separate explicit
transport consumer compatible with the newly constructed rescaled metrics.

## MC01: what the chosen route needs from arclength and Hopf–Rinow

The blueprint's full metric Hopf–Rinow assertion (lines 754–774) is broader than
proper-space geodesic existence: completeness, local compactness, and the
length property must imply properness. The midpoint modules alone do not prove
that implication. The separate generic Hopf–Rinow implementation has since
compiled and passed the independent review in hopf_rinow_review.md. It proves
this implication and exact segments without arclength reparameterization.
It is independent metric mathematics, not inherently blocked by PC migration.

General arclength reparameterization is unnecessary for the currently compiled
route. CurveMidpoint applies the intermediate value theorem directly to each
supplied continuous near-short curve and bounds its two endpoint distances by
the actual eVariationOn length. It does not replace that curve by a constant
speed parametrization. ApproximateMidpoint then constructs new Lipschitz curves
by coherent dyadic refinement using completeness alone. GeodesicMidpoint obtains
exact metric segments when properness is available. MidpointTransfer composes
these actual producers with pointed approximations. Consequently their length
closure and geodesic consumers have no missing arclength-reparameterization
premise. This bypass does not prove the standalone BBI Proposition 2.5.9 or
claim it absent from every available library.

The existing Riemannian library was inspected only as reuse evidence:

- Comparison/HopfRinow/Proper.lean:32 proves compact finite extended-distance
  balls from RiemannianMetricComplete. Its proof installs the metric's tangent
  norm, uses the inherited minimizing exponential-map theorem, and embeds the
  ball in an exponential image of a compact tangent ball.
- The same file:231 and :291 provide ProperSpace for the connected carrier's
  induced finite riemMetricSpace, the latter from a supplied smooth metric and
  RiemannianMetricComplete. Surrounding assumptions include the finite positive
  dimensional boundaryless smooth-manifold and separation/countability setting.
  They do not assert properness for an arbitrary unrelated ambient metric or
  convert infinite distances between components to finite ones.
- Metric/Comparison/CurveLengthPartition.lean:14 bounds finite sums of
  toReal riemannianEDistOf by the Riemannian speed integral for a globally C¹
  curve. This is a useful metric-length adapter ingredient, not by itself
  equality between every eVariationOn length and a speed integral or general
  reparameterization of an arbitrary rectifiable curve.

These existing geometric declarations were source-inspected, not newly compiled
against this target Mathlib or accepted as release bindings. Preserve them as
inherited reuse candidates. Binding the actual connected metric carrier,
complete metric, curve hypotheses, and length convention remains integration
work; reimplementing their Riemannian foundations is not justified by this audit.

## Evidence

The unchanged source checks in reference_checks_revision58.md and revision59
were reread. Relevant BBI locators are Definitions 7.3.17/21 and Theorem 7.3.25,
printed 256–258/PDF 271–273; Corollary 7.3.28 and Theorem 7.3.30,
printed 258–259/PDF 273–274; Proposition 2.5.9, printed 46/PDF 61; and
Proposition 2.5.22/Theorem 2.5.23, printed 49–50/PDF 64–65. KL's metric product
convention is Section 2.2, printed 19–20/PDF 14–15. The previous archived-source
and July 6, 2024 BBI errata checks are reused; no new remote errata check or
full-book reading is claimed.

Pinned Mathlib's Gluing.lean:69–191 was read for its actual metric construction
and cross-triangle arguments, and GromovHausdorff.lean:142 and :377 onward for
isometry-class identification, optimal coupling, and the GHSpace metric.

The combined targeted build of the three reviewed modules passed with 2,171
Lake jobs, including cached dependencies, on Lean 4.35.0-rc3 and Mathlib
c55e6e786f49471c72fbddbec5415808896aec1e. An independent successful stdin import
checked eleven principal constructor/theorem axiom closures and inspected
three elaborated public signatures. Each closure contained exactly propext,
Classical.choice, and Quot.sound. No reviewed Lean file was edited.

| Reviewed file | SHA-256 |
| --- | --- |
| Correspondence.lean | 8f1450a47a48753193b41148789e2b5d9a30128de05b40868a1ce308db5a5820 |
| Scaling/Rescale.lean | f43c664fa07197e1646cde8f23f6f91a5ede091aa63543c5e3cccdfdc22c02be |
| ScaledProductCollapse.lean | d14ea93a318ca449e80eadba32bf5b53544a597403e7bb85657ba2268e3b343f |
| Comparison/HopfRinow/Proper.lean, source only | 99d429c858bf47056d62525c72f1964af1319d77dc66a8e89f1d8f15abfe648c |

## Addendum: literal BBI convention and finite-net GH comparison

The complete BBIApproximation.lean and FiniteNetComparison.lean files were
independently reviewed after their implementations compiled. No mathematical
defect was found. The existing OpenBallApproximation conversion proofs were
reread as their actual consumers.

BBIApproximation uses the extended nonnegative supremum of all absolute
pairwise errors. An unbounded map cannot acquire a spurious finite real
distortion through a conditional real-supremum convention. A strict supremum
bound implies every pairwise strict bound; the reverse adapter explicitly
increases ε to η>ε, proving supremum ≤ε<η. There is no false fixed-error
equivalence between these two kinds of bound.

PointedBBIApprox has a positive radius, positive error, open source ball,
exact basepoint, strict supremum distortion, and witnessed strict-distance
coverage of the open target ball of radius R−ε. It does not require ε<R.
When ε≥R, that target ball is empty, but the other fields still apply.
The conversion from project convergence handles these tests by first choosing
δ=min(ε/2,R/2)>0. Thus no part of the source's all-positive-error quantifier
is dropped. All closed/open conversions retain their explicit radius and error
slack. Maps may vary with radius, error, and source index.

The raw BBIPointedGHConverges definition deliberately omits target completeness.
The exact proved equivalence is project convergence if and only if target
completeness and raw BBI convergence. The strict-threshold theorem also proves
the equivalence between eventual indices and the printed n>N convention.
Neither source properness nor source completeness is added.

For this addendum, the archived BBI pages printed 272–273/PDF 287–288 were
freshly text-extracted and read using the existing temporary source-reading
environment. Definition 8.1.1 indeed has independent positive R and ε, an
open-ball map, strict distortion, and the n>N threshold. The complete-limit
restriction is a separate statement on printed page 273. The retained
July 6, 2024 errata page 9 was also freshly text-extracted and read: it adds
the uniform diameter premise to Exercise 8.1.2(1) and fixes the two ε subscripts
on printed page 273. No remote-sheet retrieval or new visual inspection is
claimed by this independent addendum. The leaf author's earlier visual/source
checks and source hashes are recorded in bbi_approximations.md.

FiniteNetComparison embeds both X and its subset in the original ambient X,
using identity and the isometric subtype inclusion. It obtains the exact bound
dGH(X,S)≤ε, including ε=0, directly from Hausdorff coverage. All compactness and
nonemptiness hypotheses are present. The finite-set specialization gets
compactness from finiteness; its explicit Nonempty S is automatically available
mathematically from witnessed net coverage of nonempty X, but callers must
install that instance. Neither intrinsic subset distances nor continuous
nearest-center selections enter the proof.

The combined targeted build passed (2,166 Lake jobs including cached
dependencies). Eight independently checked definition/theorem axiom closures
contained only propext, Classical.choice, and Quot.sound; three public
signatures were inspected. Toolchain and Mathlib pin are unchanged. Source
hashes are:

| Reviewed file | SHA-256 |
| --- | --- |
| BBIApproximation.lean | c812d3b6d9c406e9cea17ea8ebf7c10032100ba7d14e252a1db5c8c614112bd5 |
| FiniteNetComparison.lean | d7935c189da6551e5c39260f446ef53e625116538f36da49ddf7f1bd3994f473 |

The node_coverage.md table was checked against the reviewed developments and
their stated remaining boundaries. MC17/MC20 retain the actual Riemannian
adapter work; MC18 retains geometric packing, comparison stability, and dimension
closure; full_chapter_complete stays false. These qualifications avoid an
overstatement of what this independent metric batch proves. The initially
pending escaping-point counterexample subsequently compiled and was reviewed
as follows, resolving the table's only staging qualification.

## Addendum: the actual escaping-point counterexample

EscapingPoint.lean was independently read in full, including its final
not_exists_uniform_diam_bound theorem. It uses the actual subtype
{0,n+1} of the real line, with the induced metric, basepoint 0, and the other
point n+1. These points remain distinct at n=0. Finite and Nonempty instances
give the required compact, nonempty source spaces without postulated diameter
or distance fields. This is the blueprint's i≥1 example with i=n+1.

When the fixed requested closed-ball radius R is less than n+1, that ball
contains only the basepoint. The constructed constant map to Unit therefore
has zero distortion and genuine coverage, proving pointed convergence for
every requested radius and admissible positive error. It is not claimed to be
a small-distortion map on the whole two-point space.

The exact diameter is n+1. The full relation gives the GH upper bound (n+1)/2;
any optimal correspondence to the singleton pairs both source points with
the same target point, giving the matching lower bound. The file consequently
proves GH distance tends to infinity, fails to tend to zero, and the source
diameters admit no uniform real bound. All three statements concern the same
actual spaces and the same metrics as the pointed-convergence theorem.
No defect was found in these claims or their quantifiers.

The independent targeted build passed (2,167 jobs including cached
dependencies). The six principal conclusion axiom closures were independently
checked; all contained exactly propext, Classical.choice, and Quot.sound.
The source SHA-256 is
0c3a035e63b330730f39aa6a19942f696c85985a44b2c462117dc57bd7c4fe95.
The source comparison is the blueprint's displayed MC11 example at lines
1220–1228 and the freshly read retained BBI errata page 9 discussed above.
No Lean source was edited during any of these independent reviews.
