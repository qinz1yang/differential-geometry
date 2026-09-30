# An escaping point: why MC11 needs a uniform diameter bound

File: `DifferentialGeometry/Geometry/Metric/Approximation/EscapingPoint.lean`.
Namespace: `GC.MetricGeometry.EscapingPoint`.

The example uses the actual two-point subsets

`Carrier n = {0, n+1} subset Real`,

with their induced real metric, basepoint `0`, and second point `n+1`.
Indexing begins at zero, so the two points are distinct even in the first
member. Each carrier is finite, nonempty, and compact. No abstract metric
or assumed GH-distance formula is used.

The proved conclusions are:

- `diam_eq_separation`: the diameter is exactly `n+1`.
- `not_exists_uniform_diam_bound`: there is no real uniform diameter bound.
- `pointed_convergence`: these pointed spaces converge to the singleton
  `Unit` under the actual `PointedGHConverges` definition.
- `ghDist_eq_half_separation`: their compact GH distance from `Unit` is
  exactly `(n+1)/2`.
- `tendsto_ghDist_atTop`: these GH distances tend to positive infinity.
- `not_tendsto_ghDist_zero`: in particular, compact GH convergence to that
  singleton fails.

For pointed convergence, every fixed closed radius-`R` ball is exactly the
basepoint once `R<n+1`. `approximation` then constructs an actual
`PointedBallApprox` to the singleton for every `0<epsilon<R`; its map,
zero distortion, exact basepoint, and coverage witness are supplied. The
strict radius condition matters: at `R=n+1`, the far point is in the closed
ball and this singleton-ball argument cannot be used.

For the upper GH bound, the universal relation to the singleton is an
actual correspondence with distortion at most `n+1`. For the lower bound,
the proved optimal-correspondence theorem relates both actual endpoints to
the singleton, forcing `n+1 <= 2*dGH`. Thus the exact formula does not
depend on an assumed converse approximation estimate.

This example shows that compactness of every source and the target, even
with proper source metrics, does not suffice for pointed convergence to
imply compact GH convergence. It validates the uniform diameter hypothesis
retained in `PointedGHConverges.tendsto_ghDist_of_uniform_diam`.

Source checks:

- `master207A.tex`, MC11, lines 1221--1228: the written escaping-two-point
  example. Reindexing the blueprint's positive integer `i` as `n+1` changes
  no mathematical assertion.
- BBI, *A Course in Metric Geometry* (2001), Definition 8.1.1 and Exercise
  8.1.2(1), printed page 272 / PDF page 287, reopened.
- Retained BBI author errata dated July 6, 2024, PDF page 9, reopened: the
  exercise requires uniformly bounded source diameters. Prior source checks
  in `reference_checks_revision59.md` and `revision60` remain applicable.
  No new remote errata retrieval is claimed.
- BBI source SHA-256:
  `4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`.
  Retained errata SHA-256:
  `68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e`.

The module built successfully without warnings against Lean 4.35.0-rc3 and
mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e` (2167 jobs). All ten
proof/approximation declarations were checked with `#print axioms`; only
`propext`, `Classical.choice`, and `Quot.sound` occur. Concrete applications
checked first-member compactness, its separation `1`, its GH distance `1/2`,
and a radius-2, error-1/10 approximation at index 5. No admissions, new
axioms, new metric foundation, or edits to other mathematical modules were
required.
