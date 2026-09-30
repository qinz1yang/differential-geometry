# Pointed-ball approximation transport

The new leaf is
`DifferentialGeometry/Geometry/Metric/Approximation/Transport.lean`.
It imports the existing `PointedBallApproximation.lean` only. No PC,
Riemannian metric, Ricci flow, curvature or manifold declarations are imported.
The existing approximation structure and existing source files are unchanged.

## Exact mathematical statements

All three declarations are definitions that construct actual approximation
maps and prove all their required properties. None assumes the desired
approximation as an extra hypothesis. Both underlying metric spaces are
arbitrary; no completeness, properness, geodesicity or nonempty typeclass is
required. The chosen basepoints themselves ensure nonemptiness.

The existing object `PointedBallApprox p q R ε` has `0 < ε < R`; its map is
defined on the source **closed** radius-R ball, sends p exactly to q, has
pairwise distortion strictly less than ε, and has ε-dense image over the
target **closed** radius-(R-ε) ball. The image need not lie in the target
radius-R ball, and continuity of the map is not assumed.

1. `PointedBallApprox.enlargeError f hεη hηR` retains exactly the same map,
   radius and basepoints when `ε ≤ η < R`, producing error η. Equality
   `η = ε` is allowed. The smaller target coverage ball is essential.
2. `PointedBallApprox.recenter f a hs hsR` assumes `3 ε < s` and
   `dist a p + s ≤ R`. It restricts the same map to the source closed
   radius-s ball at a and produces error `3 ε`, with target basepoint
   **exactly f(a)**. The hypotheses imply that a belongs to the original
   source ball, so this value is well-defined. The distance order `dist a p`
   agrees with the blueprint's `dist p a` by symmetry. Equality at the outer
   buffer, `dist a p + s = R`, is allowed. No nearby substitute target
   basepoint is permitted by this declaration.
3. `PointedBallApprox.rescale f c hc mX mY hX hY` assumes `c > 0` and
   receives explicit metric structures `mX`, `mY` on the **same** types X,Y.
   The hypotheses state for every pair that the new distance equals c times
   the original distance. It constructs the same pointwise map as an
   approximation for the new metrics with radius `c R` and error `c ε`.
   Original and new metrics are explicitly distinguished in the Lean
   signature. This is transport across supplied scaled metric structures;
   it does **not** construct a new rescaled-space type or install a global
   metric instance. It also does not assert a Riemannian tensor-to-distance
   scaling theorem. That separate adapter must account for the square root
   when a tensor is multiplied by a positive scalar.

The recentering proof first bounds the target point's distance from q, uses
the original coverage property, and then combines the original distortion
bound with that witness's approximation error to put the witness inside
the new source ball. In particular, it does not assume that arbitrary
restriction preserves coverage.

## Blueprint and source correspondence

The precise blueprint used is the copied revision207 `master207A.tex`:

- MC06, `def:metric-approx`, lines1015-1034: closed-ball approximation and
  the subsequent error-enlargement observation.
- MC10, `lem:metric-scale-recenter`, lines1102-1122: scaling and recentering,
  including the stated buffer, error factor3 and exact target f(a).

These passages and their written proofs were read for this implementation.
The unchanged primary-source comparison is reused from the existing
`metric_geometry_contracts.csv` MC10 entry and
`reference_checks_revision77.md`: BBI, *A Course in Metric Geometry*,
Section8.2/Exercise8.2.3, printed275/PDF290, and Kleiner--Lott 2014,
Section2.2, printed20/PDF15. The quantitative recentering estimate is the
blueprint's derived argument, not a numerical theorem attributed to either
source. No fresh exhaustive primary-source or errata audit is claimed.

The target Mathlib source was searched for metric rescaling constructors in
`Topology/MetricSpace`, `Topology/EMetricSpace`, and global matching names.
No replacement metric vocabulary was introduced. Supplying explicit metric
structures and distance identities keeps this leaf independent of the
eventual migrated Riemannian adapter.

## Executed verification

- `lake build DifferentialGeometry.Geometry.Metric.Approximation.Transport`
  passed on Lean `v4.35.0-rc3`, using Mathlib commit
  `c55e6e786f49471c72fbddbec5415808896aec1e`.
  Lake reported 1,246 jobs. This is a leaf build, not a whole-PC/root build.
- `#print` inspected the elaborated rescaling declaration and its actual
  function. The new and old metrics are explicit arguments in source;
  ordinary pretty-printing suppresses those instance arguments in `dist`.
- `#print axioms` for all three declarations returned only
  `propext`, `Classical.choice`, `Quot.sound`. There is no `sorryAx` or new
  mathematical axiom in their dependency closures.
- Source contains no admissions, unsafe declarations, comments or docstrings.

The broader Chapter3 implementation and its integration with the migrated
PC foundation remain separate tasks. These declarations alone do not
formalize pointed compactness, the curvature-to-model theorem, or an
actual Riemannian distance transport.
