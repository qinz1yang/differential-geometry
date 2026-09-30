# Proper approximate-midpoint spaces admit actual metric segments

The new leaf
`DifferentialGeometry/Topology/MetricSpace/GeodesicMidpoint.lean`
proves the metric-segment conclusion of MC23. It uses actual continuous
maps on the real closed interval, rather than introducing a new path,
length-space or geodesic-space class. It has no dependence on PC's
manifold or Riemannian interfaces.

## Exact statements

All spaces in these declarations are ordinary real-valued metric spaces.

- `Metric.exists_midpoint_of_approximate_midpoints`: assume X is proper.
  For fixed a,b, if every positive ε admits z with both
  `d(a,z) ≤ d(a,b)/2 + ε` and `d(b,z) ≤ d(a,b)/2 + ε`, then an exact
  midpoint m exists: `d(a,m) = d(m,b) = d(a,b)/2`.
- `Metric.exists_metric_segment_of_midpoints`: assume X is proper and
  every pair has an exact midpoint. For each a,b there is a continuous
  `f : Icc (0 : ℝ) 1 → X` with f(0)=a, f(1)=b, and
  `d(f(s),f(t)) = d(a,b) * d(s,t)` for every s,t in that interval.
- `Metric.exists_metric_segment_of_approximate_midpoints`: assume X is
  proper and the approximate-midpoint property holds for **every pair and
  every positive ε**. The same actual metric-segment conclusion follows
  for every a,b, by applying the preceding two theorems.

The two conjunctions in the approximate-midpoint hypothesis are exactly
the blueprint's condition that the maximum of the two distances is at
most `d(a,b)/2 + ε`. The orientation `d(b,z)` in that premise and
`d(z,b)` in the conclusion is converted by metric symmetry.

No local compactness, completeness, positive diameter, connectedness or
length-space hypothesis is silently added. Properness is an explicit
assumption; in this metric setting it already implies completeness, but
the implemented proof directly uses compact closed balls. The case a=b
is included without dividing by d(a,b). There is no uniqueness assertion
for the midpoint or for the resulting segment, and no claim of smoothness.

## Construction

To obtain an exact midpoint, choose approximate midpoints with errors
`1/(n+1)`. Eventually these points lie in the compact closed ball
centered at a of radius `d(a,b)/2+1`. An ultrafilter limit belongs to
that ball; continuity of distance gives the two upper bounds d(a,b)/2.
The triangle inequality makes both bounds equalities.

For the segment construction put D=d(a,b). Repeatedly split a pair at an
exact midpoint. At level n this supplies a finite chain from a to b with
`2^n` edges and each adjacent distance at most `D/2^n`. The proof handles
the splice between the two halves explicitly. Chains at different levels
need not be coherent: compactness will select their limiting behavior.

For t in [0,1], take the chain point indexed by `floor(t*2^n)`. These
step maps g(n) need not be continuous. The polygon inequality gives:

```
g(n)([0,1]) lies in the closed ball of radius D at a;
d(g(n)(s),g(n)(t)) ≤ D*d(s,t) + D/2^n;
g(n)(0)=a and g(n)(1)=b.
```

Choose one ultrafilter refining the natural-number tail filter. Compactness
of the fixed closed ball yields a limit F(t) for every t along that same
ultrafilter. Passing the displayed inequality to the limit proves that F
is D-Lipschitz and hence continuous. The endpoints are retained. The
existing proved `Metric.dist_eq_mul_of_lipschitz_interval` then upgrades
the Lipschitz bound to equality, using the endpoint distance D.

The finite-chain construction and its summation helper are private lemmas
in this file. No general public dyadic-number representation was created.

## Source correspondence and deliberate scope

Revision207 `master207A.tex`, lines1450-1612, was read, including all of
MC21, MC22 and MC23. The exact consumer is MC23,
`cor:metric-proper-midpoint-geodesic`, lines1582-1611. Its approximate
midpoint convention and its separate use of properness are preserved.

The source comparison in `reference_checks_revision68.md` was reused:
BBI2.4.7-2.4.10, printed41/PDF56, and2.4.16, printed42-43/PDF57-58;
the archived book hash is
`4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`.
That record distinguishes the exact-midpoint dyadic argument from the
approximate-midpoint exercise and incorporates the retained author errata.
No new exhaustive primary-source/errata audit is claimed here.

The implemented proof uses properness once more to take limits of
noncontinuous step maps. This replaces the written proof's coherent
dyadic dense-domain extension, without changing the MC23 conclusion.
Existing `DenseExtension.lean` and `GeodesicCompactness.lean` were read;
the latter's endpoint equality theorem is an actual dependency.

**This is not the completeness-only MC22 theorem.** MC22's continuous
near-minimizing paths in a possibly nonproper complete space, with the
specified length estimate, are supplied separately by the subsequent
`ApproximateMidpoint.lean` development; see `approximate_midpoint.md`. This file also
does not prove the pointed-limit production of approximate midpoints;
that is a separate consumer of the actual approximation maps. Its output
can be fed to `exists_metric_segment_of_approximate_midpoints` once the
limit is proper.

## Executed checks

The leaf build passed on Lean `v4.35.0-rc3` with Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`, reporting 1,963 jobs.
This does not claim a whole-root or migrated-PC build.

The three public theorem types/axiom closures were checked. Their axiom
closures contain only `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx` or new mathematical axiom. The Lean source has no
admissions, unsafe declarations, comments or docstrings.
