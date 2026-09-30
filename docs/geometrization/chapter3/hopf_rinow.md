# Metric Hopf--Rinow: MC01

File: `DifferentialGeometry/Topology/MetricSpace/HopfRinow.lean`.

## Actual statements

`Metric.properSpace_of_arbitrarily_short_curves` has the following contract.
Let `X` be a complete, locally compact metric space. Suppose that for every
pair `a,b` and every positive real `epsilon`, there is a continuous curve
`c : [0,1] -> X`, with endpoints `a,b`, whose actual partition variation
`eVariationOn c univ` is strictly less than `dist(a,b)+epsilon`. Then `X`
is proper: **every closed metric ball is compact**.

All distances are finite real distances. The curve hypothesis is spelled
out in the declaration; it is not a package that already assumes properness,
compact balls, or minimizing paths. Closed balls have their ambient metric.
They are not assumed to be length spaces. Neither a chosen basepoint nor
nonemptiness is an extra hypothesis.

`Metric.properSpace_of_approximate_midpoints` gives the same conclusion from
complete + locally compact + the approximate-midpoint property:

`forall a b epsilon>0, exists z,
dist(a,z) <= dist(a,b)/2 + epsilon and
dist(b,z) <= dist(a,b)/2 + epsilon`.

This second theorem uses the already proved complete approximate-midpoint
construction in `ApproximateMidpoint` to supply the actual near-short curves.

`Metric.exists_metric_segment_of_locallyCompact_of_arbitrarily_short_curves`
then gives, for every `a,b`, a continuous map `f : [0,1] -> X` with the exact
endpoints and

`dist(f(s),f(t)) = dist(a,b) * dist(s,t)`.

This is the minimizing constant-speed segment conclusion, including
coincident endpoints. It asserts neither uniqueness of the minimizer nor
that every locally minimizing geodesic is globally minimizing.

## Proof implemented

1. **Actual radial trimming.** A near-short curve from `p` to `y` meets the
   prescribed distance level `r` by the intermediate value theorem. The
   two-piece variation bound controls its remaining distance. Precisely,
   for `r,delta >= 0`, `eta>0`, and `dist(y,p)<=r+delta`, the code constructs
   `z` with `dist(z,p)<=r` and `dist(y,z)<delta+eta`. If `y` already lies in
   the smaller ball, use `z=y`. No distance infimum is assumed attained and
   no preexisting geodesic is used.
2. **Compact-ball enlargement.** A compact ball has a compact closed
   thickening of some positive radius by local compactness. The preceding
   radial trimming, with strict slack, puts a slightly larger closed ball
   inside this compact set. Its closedness makes it compact.
3. **No finite maximal radius.** Local compactness supplies an initial
   positive compact-ball radius. If the set of these radii were bounded,
   take its real supremum. At every accuracy, select a smaller compact ball
   with radius sufficiently close to that supremum. Radial trimming and a
   finite net in the smaller ball give a finite net in the supremum ball.
   Completeness makes that closed, totally bounded ball compact. Step 2
   gives a compact ball with radius strictly larger than the supremum, a
   contradiction. All radii, including nonpositive radii, are handled by
   inclusion in a larger positive compact ball.
4. **Exact segments.** Properness and the near-short-curve midpoint theorem
   feed the previously proved `GeodesicMidpoint` construction. This route
   does not reparameterize an arbitrary supplied rectifiable curve.

Thus a general arclength-reparameterization theorem is unnecessary for this
implemented route to the stated properness and geodesic conclusions. It is
not being reported as proved by this file. The connection from PC's
Riemannian manifold types to these finite metric and near-short-curve
hypotheses remains a separate foundation adapter.

## Sources actually read

- Blueprint `master207A.tex`, MC01, lines 660--781, especially the
  source-qualified metric Hopf--Rinow statement and compact-radius proof
  plan at lines 754--777.
- Burago--Burago--Ivanov, *A Course in Metric Geometry*, 2001 English book:
  Definition 2.5.21, Proposition 2.5.22 and its **full proof**, and Theorem
  2.5.23, printed pages 49--50 / PDF pages 64--65, reopened for this proof.
  Also reopened the adjacent definitions and qualifications through printed
  page 51 / PDF page 66. The book's full theorem 2.5.28 concerning extension
  of naturally parameterized geodesics is not claimed here.
- The archived BBI PDF identity is SHA-256
  `4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`.
- Retained author errata dated July 6, 2024, PDF pages 2--4, reopened.
  The finite-distance qualification for Sections 2.4--2.5 is enforced by
  `MetricSpace`. The removal of local compactness before the approximate
  midpoint criterion does **not** remove the necessary local compactness
  assumption from this properness theorem. No separate correction to
  Proposition 2.5.22 or Theorem 2.5.23 occurs on these inspected pages. The
  natural-parameter qualification of Theorem 2.5.28 is outside our claim.
  Errata identity: SHA-256
  `68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e`.
  Prior source/errata records `reference_checks_revision58.md`,
  `reference_checks_revision59.md`, and `reference_checks_revision68.md`
  are retained; no fresh remote errata retrieval is claimed.

The proof retains BBI's compact-radius argument but replaces any compressed
claim identifying a thickened ball with a larger ball by a proved
approximate trimming statement with explicit margins. The final minimizing
segment uses the already formalized midpoint route rather than the book's
curve reparameterization and minimizing-sequence route.

## Lean verification

The module built successfully against Lean 4.35.0-rc3 and mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e` (1971 jobs), without warnings.
All five public theorems were checked with `#print axioms`; they depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

Additional compiled applications checked the singleton space, the empty
space, and radial trimming at radius zero with coincident endpoints. The
complete/local-compact/curve assumptions and exact-segment conclusion were
also inspected from Lean's fully elaborated signatures. No admission,
new mathematical axiom, PC import, or manifold-foundation change was used.
