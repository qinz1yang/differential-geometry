# Global metric line splitting: exact contract and source comparison

This development proves the metric content of blueprint 207 ALS01–ALS05,
including AC43's actual aligned onto splitting. It also applies that theorem
to the same limit produced by the existing Chapter 3/4 extraction theorem.
The ten added modules use Lean 4.35.0-rc3 and the unchanged pinned Mathlib.
All previous mathematical leaf files and all blueprint TeX files are preserved.
This does not complete Chapter 4, establish a line in a particular collapsed
limit, or produce global comparison from local Riemannian curvature bounds.

## Mathematical theorem, without Lean notation

Let X be a proper metric space in which every pair of points admits a
constant-speed minimizing segment. Suppose that X satisfies the global
Euclidean four-point comparison inequality: at every center, the sum of the
three comparison angles made by three outer points is at most 2π. Each
outer point must differ from the center; outer points may repeat.
Let γ:ℝ→X be a specified isometric embedding of the entire real line.

There is a metric space Y, a point p in Y, and a bijective isometry

    α:X → ℝ × Y,      α(γ(t)) = (t,p) for every real t,

where the product has distance sqrt((s−t)²+dY(y,z)²). The space Y is proper,
complete, geodesic, and satisfies the same global four-point comparison.
Its Hausdorff dimension is at most that of X, including extended-real
infinite dimension. No finite-dimension assumption is required.

This is `exists_isometryEquiv_real_prod` in the namespace
`DifferentialGeometry.Geometry.Comparison.Toponogov`. Properness implies
completeness; the supplied line implies nonemptiness. Thus their omission
as separate assumptions does not weaken the intended conclusion.

The exact geodesic input is: for all a,b∈X there exists a continuous map
f:[0,1]→X with f(0)=a, f(1)=b, and
`d(f(s),f(t))=d(a,b)|s−t|` for all s,t. This is literally the segment
contract already returned by `ComparisonLimit.lean`, including a=b.
Neither a smooth structure nor a Riemannian metric is used.

## Actual maps and the proof boundary

Define

    b(x) = (d(x,γ(0))² + 1 − d(x,γ(1))²)/2.

The following are proved, not assumed:

| Blueprint node | Proved mathematical content | Principal Lean declarations |
|---|---|---|
| ALS01 | Shortening either positive comparison-angle arm can only increase its angle. The existing side-comparison theorem supplies the other part. | `metricComparisonAngle_le_of_shortening_right`, `_left` |
| ALS02 | For every x there is a unique pair (b,h), h≥0, with d(x,γ(t))²=(t−b)²+h² for every real t; γ(b) is the unique closest point on the line. | `existsUnique_line_distance_parameters`, `existsUnique_nearest_point_on_isometry_line` |
| ALS03 | b is 1-Lipschitz, equals t on γ(t), and is affine on every minimizing segment. Every point lies on a unit-speed line ℓx with ℓx(0)=x and b(ℓx(t))=b(x)+t. | `lipschitzWith_lineCoordinate`, `lineCoordinate_affine_of_dist`, `exists_calibrated_line` |
| ALS04 | Those oriented lines are unique; the full two-line cross-distance law holds. Ft(x)=ℓx(t) is an isometry with F0=id and FsFt=Fs+t. | `calibrated_line_unique`, `sq_dist_calibrated_lines`, `lineTranslation_add`, `isometry_lineTranslation` |
| ALS05 / AC43 | Y is the actual zero slice b⁻¹(0) with the restricted metric; the displayed α is an aligned onto isometry, and Y retains all the stated geometry. | `lineSplitting`, `lineSplitting_apply_line`, `exists_isometryEquiv_real_prod` |

The constructed maps are `α(x)=(b(x),F−b(x)(x))` and `α⁻¹(t,y)=Ft(y)`.
The term `lineSplitting` has type `IsometryEquiv`, so an actual inverse and
both inverse identities are part of the checked term. Its target is
`WithLp 2 (ℝ × Y)`, never Lean's default maximum-metric Cartesian product.
The second component follows the line through x, as the BBI erratum requires.
`lineSplitting_fst` identifies its first coordinate exactly.

All-point line construction uses properness and the supplied exact segments.
Earlier distance-to-line and coordinate results do not need properness,
completeness, finite dimension, or general geodesic existence. Angle
monotonicity even works on an arbitrary subset carrying the relevant
four-point inequalities and explicit segment-distance identities. These are
proved strengthenings, not unstated assumptions about arbitrary subsets.

## Proof improvement and audit points

ALS02 has a shorter algebraic proof than the blueprint's angle-limit proof.
For fixed x, side comparison makes f(t)=d(x,γ(t))²−t² concave on all of ℝ.
Triangle inequality gives d(x,γ(t))+d(x,γ(−t))≥2|t|; the elementary square
inequality gives f(t)+f(−t)≥0. A globally nonnegative concave real function
is constant. Applying this to the even part of f and reflecting the
concavity inequality makes every convex-combination inequality an equality.
Thus f is affine. Values at 0 and 1 give the displayed b exactly.
The constancy step reuses the existing
`DifferentialGeometry.eq_of_concaveOn_univ_of_bddBelow` in
`Analysis/Convex/Concavity.lean`, which compiled unchanged on this target.
`Analysis/Convex/Affine.lean` adds the nonnegative corollary and reflected
affineness argument. Exact reuse provenance is in the source record.

The 1-Lipschitz bound likewise follows from finite quadratic inequalities
and the triangle inequality at γ(−r) for all r≥0. Segment affineness follows
by comparing with γ(T) for every positive and negative T: an affine
expression nonnegative for every real T must have zero slope.

For ray extraction take endpoints γ(b(x)+n+1) and segments from x to them.
Their lengths Ln satisfy n+1≤Ln≤n+1+h, where h=d(x,γ(b(x))). At ray parameter
t the segment fraction is min(t/(n+1),1). Its speed Ln/(n+1) tends to 1;
its b-coordinate is eventually exactly b(x)+t. One fixed ultrafilter finer
than the tails is used for every t, and properness supplies all pointwise
limits in compact balls. This preserves every pairwise distance and yields
an actual isometric ray. A second ray using the reversed original line is
joined to it; the Lipschitz bound on b supplies the cross-half lower bound.

The exact two-line law then proves uniqueness, translation composition and
the Pythagorean product identity. The zero slice is closed by continuity and
contains γ(0); affineness keeps every ambient minimizing segment between
its points inside the slice. Four-point inequalities use unchanged subtype
distances. Dimension uses the isometric inclusion and monotonicity of
Mathlib's actual Hausdorff dimension, without product-dimension equality.

Corner cases checked in the proofs include repeated outer points, collinear
triangles, shortening fraction 1, zero transverse distance, coincident
parallel lines, t=0, both signs of all line parameters, constant geodesic
segments, and a singleton transverse factor. The shortening fraction is
strictly positive: there is no angle claim with an arm collapsed to its
center. A ray is never used as a substitute for the input two-sided line.

## Same-limit downstream application

`GC.MetricGeometry.PointedGHConverges.exists_isometryEquiv_real_prod`
consumes actual pointed convergence, eventual source comparison on each
fixed-radius ball with κi≥0 tending to zero, properness and exact segments
on the target, and an actual isometric line in that target. It proves an
aligned splitting of that very target and retains all the factor properties.
The convergence basepoint need not equal γ(0); pointed alignment is with
γ(0). If they agree, the existing basepoint is preserved exactly.

`GC.MetricGeometry.exists_pointedGHConverges_with_line_splitting` composes
the previously proved extraction theorem with splitting. Its inputs are
actual polynomial covering estimates, near-short continuous curves, and
the same eventual source comparison estimates. It produces one subsequence,
metric target and basepoint, retaining properness, convergence, dimension,
comparison, and exact geodesics. For **every subsequently supplied actual
line in that same target**, it gives the aligned onto splitting and a factor
with all those intrinsic properties and dimension bounded by the original
covering exponent. The limit and subsequence are chosen before the line.
No completeness or properness of the source spaces is assumed.
This is a checked supplier-to-consumer application, not a claim that every
such limit contains a line. A compact or point limit remains allowed.

## Sources actually checked

- Blueprint `master207A.tex`, ALS01–ALS05, lines 6731–7020, labels recorded
  verbatim in `evidence/line_splitting_sources.json`; AC42–AC45, lines
  4254–4418. The current DAG's original statements/statuses are preserved.
- Burago–Burago–Ivanov, *A Course in Metric Geometry*, AMS 2001, GSM 33,
  Theorem 10.5.1, Definition 10.5.3, Lemmas 10.5.4 and 10.5.6, Corollary
  10.5.5 and the full three-step splitting proof, printed 366–369 / PDF
  381–384. Archived bytes SHA256
  `4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`.
- Retained author errata, July 6, 2024, PDF 13: plane lines in Definition
  10.5.3 are parallel; the p367 chain uses the distance between the fixed
  corresponding points; the p369 transport follows the line through x.
  SHA256 `68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e`.
- Revision138's source comparison and correction records are reused for
  unchanged claims. The targeted source-body and retained-errata reading from the preceding
  recommendation is reused; their hashes were rechecked in this implementation
  turn. The current blueprint and complete new proofs were reread. This is
  not a full-book audit. That revision's failed remote
  retrieval remains a limitation: no fresh verification of current remote
  errata bytes or exhaustive correction clearance is claimed.

The concavity proof of ALS02 and finite-inequality Lipschitz proof are this
implementation's departures from the written route; they are not attributed
as verbatim BBI arguments. The proof retains BBI's corrected parallel-line
and actual-slice conventions and avoids its compressed projection argument.
No new imported metric splitting axiom, gradient-flow theorem, or PC adapter
was introduced. The generic splitting module imports Mathlib's general
`WithLp.prod_dist_eq_add` directly, so it has no dependency on the pointed
compactness or product-collapse modules. Mathlib's specialized
`prod_dist_eq_of_L2` requires additive normed structures and cannot be used
for an arbitrary transverse metric space. Existing Riemannian splitting declarations have smooth
manifold hypotheses and were not substituted for a singular metric limit.

## Verification and remaining work

Run the existing `python3 tools/gc/check_chapter3.py` for all accepted new
modules and their entire axiom closures. Its receipt, not the mere presence
of a declaration, records build acceptance. The supplemental reproducible
review is `python3 tools/gc/check_line_splitting.py`; its declaration inventory
uses the existing provenance mechanism and binds the above DAG nodes to
actual elaborated signatures and supplier applications. See
`line_splitting_review.md` and the evidence receipts for executed results.

Local-to-global comparison, curvature-to-covering estimates, lines and
higher-rank configurations on the actual collapse limits, and the ensuing
strainer, cone, local-model and smooth flow interfaces remain separate work.
Old admitted skeleton statements are unchanged; none is marked discharged
merely because a new independent metric theorem has been proved. Blueprint
revision 207 remains the current Overleaf version.
