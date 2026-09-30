# KL approximations and the closed-ball convention

`DifferentialGeometry/Geometry/Metric/Approximation/KleinerLottApproximation.lean`
implements the positive-parameter part of KL Definition 3.2 and the
quantitative conversions in blueprint MC11.

## Exact mathematical content

`GC.MetricGeometry.KleinerLottApprox p q δ` requires `0 < δ < 1` and contains:

- a map `f : X → Y` on the whole source space;
- the exact basepoint identity `f p = q`;
- non-strict pairwise distortion `≤ δ` for points in the open ball
  `B(p,δ⁻¹)`;
- non-strict distance-to-image control
  `Metric.infDist y (f '' B(p,δ⁻¹)) ≤ δ` for points in the open target
  ball `B(q,δ⁻¹−δ)`.

The definition uses the actual infimum distance, not an already-chosen
coverage witness. Continuity of the map is not required. The source's
zero-parameter endpoint is not encoded using real inversion at zero;
this structure covers exactly the positive parameters used by MC11's
convergence comparison.

`KleinerLottApprox.image_nonempty` proves that the tested image contains
the target basepoint. Consequently, `coverage_witness` can apply
Mathlib's `Metric.infDist_lt_iff` with a nonempty image and prove an
actual witness at distance **strictly less than `2δ`**. No attainment
of the infimum at distance `δ` is asserted.

`KleinerLottApprox.toClosedBall` takes `3δ < R < δ⁻¹` and produces
`PointedBallApprox p q R (3δ)`. The proof of coverage starts from a
point of the closed target ball of radius `R−3δ`. The witness bound
and radial distortion put its source preimage strictly inside radius
`R`. Thus source membership is proved even for target boundary points.

Conversely, `PointedBallApprox.toKleinerLott` takes
`PointedBallApprox p q (δ⁻¹ + δ) (δ/4)` together with `0 < δ < 1`.
Its whole-source map agrees with the given map on the open ball
`B(p,δ⁻¹)` and equals `q` outside that ball. For a tested target point,
the closed approximation's witness lies strictly inside `B(p,δ⁻¹)`;
hence it remains in the tested image of the extended map. Its distance
is less than `δ/4`, which implies the required infimum bound `≤ δ`.

These are explicit conversions with changed errors and radii. They do
not identify fixed-parameter predicates or assert symmetry at the same
parameter. Selecting a single sequence of parameters tending to zero
belongs to the separate convergence development. No completeness,
properness, or curvature assumptions enter these numerical conversions.

## Source and reuse evidence

- Blueprint `GEOMETRIZATION_BLUEPRINT/master207A.tex:1133`, proposition
  `prop:metric-conventions`, especially its proof through line 1211.
- Kleiner–Lott, *Locally collapsed 3-manifolds*, Astérisque 365 (2014),
  Definition 3.2 and equation (3.3), printed page 21 / PDF page 16;
  adjacent scope discussion printed page 22 / PDF page 17. Both pages
  were reopened. Archived filename `KleinerLottAsterisqueLocalCollapse.pdf`,
  SHA-256 `7a860b4dd95b35fe33b06bf040100ec243d72c80528d927f4763391aaf79cb6e`.
- `reference_checks_revision60.md:10` records visual inspection of
  equation (3.3), verifying both non-strict inequalities. Text extraction
  misreads these signs. That unchanged visual check is reused.
- The same record, line 15, verifies the 2015-05-15 author correction
  sheet and notes no correction to Definition 3.2. This implementation
  reuses that source check; it does not claim a new exhaustive errata
  audit.
- The slack in passing from an infimum to a witness is the blueprint's
  explicit correction to the informal witness selection following KL's
  definition; it is not attributed to an author erratum.
- The target Mathlib and DifferentialGeometry were searched for an
  existing equivalent pointed approximation structure. The existing
  closed-ball structure is reused. Distance-to-image lemmas are reused
  from Mathlib's `Topology/MetricSpace/HausdorffDistance.lean`.

## Executed verification

On Lean `4.35.0-rc3`, Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`, the scoped Lake build of
`DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation`
passed, with 1,693 jobs including cached dependencies and no warnings.
A separate stdin Lean invocation audited all five authored
theorems/constructors in this module. Each uses exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or added axiom.
The module contains no comments or docstrings and imports no PC geometry.

The companion open-ball module's two radial theorems and two conversion
constructors were audited in the same invocation with the same three
standard axioms. These are scoped metric checks, not a whole-library
build or a completed PC migration.
