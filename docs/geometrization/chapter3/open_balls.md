# Open and closed pointed approximation domains

`DifferentialGeometry/Geometry/Metric/Approximation/OpenBallApproximation.lean`
implements the open-ball convention used in the proof of MC11 in
`GEOMETRIZATION_BLUEPRINT/master207A.tex:1133`.

`GC.MetricGeometry.PointedOpenBallApprox p q R ε` consists of positive
`ε < R`, a map from the open source ball `B(p,R)` to the target, exact
basepoint preservation, pairwise distortion strictly below `ε`, and
actual coverage witnesses within distance strictly below `ε` for every
point of the open target ball `B(q,R−ε)`. The map need not be continuous.

Two constructors preserve the actual restricted map and its coverage:

- `PointedOpenBallApprox.toClosedBall`: an open approximation with
  radius `R` and error `ε` gives a closed approximation with radius `s`
  and error `2ε`, provided `2ε < s < R`.
- `PointedBallApprox.toOpenBall`: the same parameter conditions turn
  a closed approximation at `(R,ε)` into an open one at `(s,2ε)`.

The coverage proofs use radial distortion and the triangle inequality
to put the original witness strictly inside radius `s`. The first
constructor includes coverage of the entire closed target ball, including
its boundary. Source and target metrics are ambient restricted metrics;
no length-space, completeness, properness, or compactness hypothesis is
introduced.

This open convention has pointwise strict distortion. It is the
blueprint's intermediate convention, not an assertion that BBI's
strict-supremum definition or KL's non-strict infimum-coverage definition
is identical at fixed parameters. Comparing convergence notions uses
these conversions together with error slack and larger initial radii.

The source records `reference_checks_revision58.md` and
`reference_checks_revision60.md` document the BBI comparison and the
actual inequalities in KL Definition 3.2. Relevant blueprint MC11 text
and these unchanged checks were reread. The KL page was reopened for
the separate KL converter. No new claim about BBI's complete metric
topology or a complete proof of its entire Section 8.1 is made here.

Mathlib and DifferentialGeometry were searched before introducing the
open structure; the existing closed `PointedBallApprox` is reused.
The new file imports only that existing pure-metric leaf.

Verification on Lean `4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`:
`lake build DifferentialGeometry.Geometry.Metric.Approximation.OpenBallApproximation`
passed (1,246 jobs including cached dependencies), with no warnings.
There are no admissions, added axioms, source comments, or docstrings.
This is a scoped metric-module build, not a PC migration or a whole-library build.
