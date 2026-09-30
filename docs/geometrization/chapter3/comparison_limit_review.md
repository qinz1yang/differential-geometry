# Independent review of the comparison limit and combined extraction

This review covers `Geometry/Metric/Approximation/ComparisonLimit.lean`,
`Geometry/Comparison/ModelAngle.lean`, and
`Geometry/Comparison/FourPoint.lean`, all under `DifferentialGeometry`.
The reviewer implemented `FiniteConfiguration.lean`; the other three
leaves and the earlier dimension extraction were written by other agents.

## Mathematical review

No mathematical defect was found in the reviewed statements or proof
route. The transfer theorem is a conditional comparison theorem on an
already specified pointed limit. The extraction theorem combines proved
metric consequences of explicit covering, length, and comparison
assumptions. Neither is presented as the full geometric producer MC18.

The source assumptions of
`PointedGHConverges.fourPointComparison_zero_of_eventual_comparison` are:

1. The actual project pointed convergence of the given metric sources
   and basepoints to the given metric target and basepoint.
2. A nonnegative real sequence `kappa i` tending to zero.
3. For every fixed positive `R`, eventually every source quadruple in
   its ambient open `R`-ball satisfies comparison at curvature
   **minus** `kappa i`.

The third assumption's eventual threshold may depend on `R`. No common
threshold for all radii is asserted. The four-point predicate requires
each outer point to differ from the central point; the outer points may
coincide. The proved `fourPointComparison_of_distinct` adapter converts
the blueprint's four-distinct-point hypothesis to this convention for
nonnegative `kappa`. In a repeated-outer-point case one angle is zero
and the other two are each at most pi. The adapter checks all three
possible equalities and needs no geometric curvature assumption for
these repeated cases.

The proof fixes a target quadruple and chooses
`M = 1 + sum of the four target radii`. This valid bound replaces the
blueprint's maximum without changing the conclusion. Approximation
errors are positive, less than `1/4`, and tend to zero. A strictly
increasing sequence of indices satisfies both the approximation and
comparison requirements. Actual lifted points belong to the source
closed `(M+2)`-ball, strictly inside the comparison open `(M+3)`-ball.

All six lifted distances converge to their target distances. The three
central target distances are positive, so their lifted versions are
eventually positive. No separation of the outer target points is
needed. Comparison is applied to those actual source points, and the
three angles pass to curvature zero jointly with their side lengths.
The closed scalar inequality survives the limit.

The auxiliary increasing sequence may depend on the chosen quadruple.
This is legitimate: every application retains the same target metric
and points. There is no claim of one auxiliary sequence working
simultaneously for all target quadruples.

`fourPointComparison_zero_of_growing_balls` is a direct checked
interface adapter: it assumes comparison for ambient balls of radii
`rho i` tending to infinity, eventually in the source index. For each
fixed radius it intersects that premise with the eventual condition
`R <= rho i` and restricts the four-point predicate to the smaller
ball. Initial radii may be nonpositive. The premise is actual ambient
four-point comparison on those balls, not merely a local curvature
statement there. The latter still requires the geometric globalization
and metric-translation producer.

## Model-angle conventions and degenerate cases

`comparisonAngleNegCurvature kappa a b c` is the angle opposite the
third side `c` with adjacent sides `a,b`. When `kappa >= 0`, its
geometric curvature is `-kappa`. At zero it is the existing Euclidean
comparison angle. At positive `kappa`, its hyperbolic formula uses
`sqrt kappa` times each side; this agrees with the pinned AKP scaling
and cosine law.

The function is total as a real formula. Its geometric interpretation
requires the side conditions, and negative input `kappa` is not claimed
to represent a positively curved model. The public cosine theorem
checks the actual triangle inequalities and positivity of the adjacent
sides; it proves the hyperbolic ratio is in `[-1,1]`, so arccos does
not change the cosine-law value by truncation.

The continuity proof removes the singularity at zero curvature. Its
regularized denominator tends to `a*b`, which is positive at the limit.
The source curvature may equal zero infinitely often. Continuity of
arccos handles angles zero and pi, including collinear triangles and
coincident outer points. The stronger analytic continuity statement
does not need triangle inequalities because it concerns the total
formula; every use in the metric transfer supplies genuine distance
triples.

The final endpoint lemmas also prove the angle is pi when the opposite
side is the sum of two positive adjacent sides, zero when it is their
absolute difference, and zero for equal adjacent sides with opposite
side zero. Symmetry in the adjacent sides is proved for the total
formula. These statements agree with the Euclidean and hyperbolic
degenerate triangles, include `kappa=0`, and support the distinct-point
adapter without imposing artificial pairwise-distinct hypotheses on
the limit theorem.

## Point-on-side comparison

`quadratic_side_comparison_of_fourPointComparison` assumes only the
zero-curvature four-point predicate on a subset and four points in that
subset. If `t` lies in `[0,1]` and

`dist a z = t * dist a b`,
`dist z b = (1-t) * dist a b`,

then it proves

`(1-t)*dist v a^2 + t*dist v b^2 - t*(1-t)*dist a b^2 <= dist v z^2`.

The inequality has the lower-curvature sign. It applies to every
point on every proportionally parametrized minimizing segment; no
uniqueness or chosen segment is assumed. The proof handles a constant
side, `t=0`, `t=1`, and `v=z` before dividing by any side length. For
an interior point and `v` distinct from it, the straight comparison
angle equals pi, the remaining two angle sum is at most pi, and the
cosine formulas give the claimed weighted square inequality. Cases
`v=a` and `v=b` remain valid in this argument since repeated outer
points are permitted.

## The single combined limit

`exists_geodesic_pointedGHConverges_of_covering_and_comparison` first
uses the already proved dimension extraction theorem. It retains that
theorem's exact target type, metric instance, basepoint, and strictly
increasing source subsequence. The comparison assumptions and curvature
convergence are transported along this same source subsequence; the
comparison transfer then supplies its new target conclusions.

Its covering hypothesis has the order
`for every R > 0, there exists C > 0, for every mesh in (0,1], eventually`
followed by an actual internal finite net with cardinality at most
`C * mesh^(-d)`. Thus the constant is independent of the mesh and
source index after their appropriate threshold, while the threshold may
depend on both radius and mesh. The dimension exponent is one fixed
nonnegative real number.

The length premise gives actual continuous curves of variation length
less than distance plus arbitrary positive error between every pair
in every source. It is an explicit metric interface, not an unstated
import from a changing manifold foundation.

The output is one proper metric target, complete by its actual
`PointedGHConverges` witness, with Hausdorff dimension at most `d`,
global zero-curvature four-point comparison, actual minimizing metric
segments, and the point-on-side square inequality. No source properness,
source completeness, target dimension, target curvature, or continuity
of approximation maps is assumed in addition to the displayed inputs.

## Current blueprint route and source evidence

Read the blueprint AC34--AC37 statements and proof bodies, the MC18
source statement, and ALG06--ALG07 at `master207A.tex`, lines
7536--7613. Read the existing source records
`reference_checks_revision69.md`, `reference_checks_revision138.md`,
and `reference_checks_revision140.md` in full. These records retain
BBI Proposition 10.7.1 (printed 376 / PDF 391), the one-way
four-point-to-side algebra from BBI 10.1.1 (printed 353 / PDF 368),
and the relevant dated author corrections. This review reuses those
scoped source checks; it does not claim a new full reading of the BBI
book or a fresh remote errata certification.

Freshly reopened the retained AKP `model.tex` body at lines 6--34,
71--95, and 174--211, branch `vol1`, commit
`ed6a16eb2a3c66c1f0f54b183bd1a4176e78b245`. Its SHA-256 is
`db849cb9a051e0c3f8ec335942c954f14223c542eee1a40c4bca4ea2a63af9f8`.
The retained BBI July 6, 2024 correction sheet was rehashed as
`68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e`.
The AKP opposite-side versus adjacent-side ordering was checked
explicitly against the Lean formula.

The current source-comparison producer is ALG06--ALG07's **256R**
route. The historical AC36 `16R` local input is not silently accepted.
For this implementation's comparison ball `(M+3)`, the corresponding
future geometric buffer is `256*(M+3)`. The original growing-radius
assumption can provide that larger fixed buffer eventually, separately
for each target configuration. Source local-to-global comparison,
intrinsic-to-ambient agreement, and production of the covering estimates
remain distinct Lean obligations. The transfer theorem assumes their
explicit outputs; it does not hide them in a new definition of curvature.

## Independent verification

After the final endpoint, distinct-point, and growing-ball adapters were
written, the reviewer independently ran
`lake build DifferentialGeometry.Geometry.Metric.Approximation.ComparisonLimit`.
It passed with 2698 Lake jobs and no warnings. This is a scoped build of
the relevant dependency tree on Lean 4.35.0-rc3 / mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, not a build of the full PC root.

The reviewer then imported that leaf through `lake env lean --stdin`
and printed the axiom closures of all 17 public declarations in the
three reviewed modules. Every closure contains only `propext`,
`Classical.choice`, and `Quot.sound`; there are no mathematical axioms
or admissions in those closures. The parent's full scoped check records
all owned declarations, including private helpers and generated ones,
separately.

Reviewed and independently built source identities:

- `ComparisonLimit.lean`:
  `a96b4ffdacc43eb08ff92eacbd0eb6f0e8d5cf305104109d8fbef74569e7b71b`.
- `ModelAngle.lean`:
  `eb1d2524535435874502aff4690ba71516faef86f34881d1dbe09eed30fd5877`.
- `FourPoint.lean`:
  `dc31e8b986c2d13899992b9c5a219dd392e3ae23a7626f3a78ac4ef301143344`.

One earlier closure invocation coincided with an author's dependency
rebuild and encountered a temporarily absent object file. The final
successful build and closure invocation above were run after those
edits; the earlier attempt is not counted as verification.
