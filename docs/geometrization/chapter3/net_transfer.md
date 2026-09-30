# Internal finite-net transfer: AC38

File: `DifferentialGeometry/Geometry/Metric/Approximation/NetTransfer.lean`.

`GC.MetricGeometry.PointedBallApprox.exists_internal_finset_net` implements
AC38 with the actual project approximation object. Its inputs are:

- metric spaces `X,Y`, basepoints `p,q`, and an actual
  `PointedBallApprox p q (R+2) epsilon`;
- `R>0`, `delta>0`, `epsilon<1/4`, and `epsilon<delta/8` (positivity of
  `epsilon` is already a field of the approximation);
- a finite set `F` inside the source closed `(R+1)`-ball;
- witnessed coverage of that entire source ball by `F` at distance at most
  `delta/4`.

It produces a finite set `T` of target points with all three properties:

1. `T.card <= F.card`;
2. every point of `T` is in the target closed `R`-ball;
3. every point of that closed ball is at distance **strictly less than**
   `delta` from some point of `T`.

Thus any assumed bound `F.card<=N` transfers to `T.card<=N`, by ordinary
transitivity. There is no positivity assumption on `N` and no forced extra
point in the output. In the pointed positive-radius application, an empty
source net cannot satisfy the source coverage hypothesis; the theorem does
not hide that fact by assuming `N>=1`.

The auxiliary theorem
`Metric.exists_internal_finset_net_of_finite_centers` is stated for arbitrary
subsets of a pseudometric space and finite families of external centers.
An external strict `eta`-cover gives an internal strict `2*eta`-net with no
increase in cardinality. This includes empty target sets and empty center
families and does not require a nonempty ambient space.

## Proof and interface details

Coverage lifts a target point of radius at most `R` to an actual point in
the approximation's source domain. The exact basepoint and distortion
bounds put this preimage strictly inside the source `(R+1)`-ball. A source
net point is also in the approximation domain. Its image is at distance
less than `delta/4 + 2*epsilon < delta/2` from the target point.

Those image centers need not lie in the target ball. The auxiliary theorem
filters out the centers whose open `delta/2`-balls do not meet the target
ball, chooses one point in each remaining intersection, and takes the
finite image of these choices. Two points in one such open ball are at
distance strictly less than `delta`. Duplicate choices may reduce the
cardinality, so the assertion is an upper bound rather than an equality.

No continuity of the approximation, compactness, completeness, properness,
length property, curvature, dimension, or fixed metric carrier across the
two spaces is assumed. Balls use their ambient distances. The construction
does not claim that their intrinsic length metrics agree with those
ambient distances.

For AC40, this theorem is applied only after selecting the radius, mesh,
approximation accuracy, and one source index satisfying the geometric net
and approximation requirements simultaneously. AC38 does not itself
provide the geometric net estimates or the eventual common-index choice.

## Sources and scope

The exact statement and full proof at `master207A.tex`, lines 4075--4107,
were read, together with all of `reference_checks_revision70.md`. That
record's unchanged source checks and errata comparisons are reused.

AC38 is the blueprint's elementary metric transfer argument; it is not
presented as a verbatim BBI theorem. Revision70 records the broader
dimension argument's sources: BBI Definitions 1.7.7--1.7.8 and
1.7.17--1.7.19, printed pages 19--23 / PDF pages 34--38, and the packing
comparison in Lemma 10.9.2, printed pages 390--391 / PDF pages 405--406.
Those results are not imported as assumptions of this transfer lemma.

The retained BBI source identity is SHA-256
`4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`, and the
retained July 6, 2024 author errata identity is
`68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e`.
No new edition, external errata retrieval, or reading of unrelated source
passages is claimed. The present module proves AC38; the Hausdorff-measure
and dimension conclusions in AC39--AC40 are separate developments.

## Verification

The module built against Lean 4.35.0-rc3 and mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e` (1248 jobs), without warnings after
updating the dependent-if API name. Both public declarations' axiom
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.

Compiled applications checked an empty target set with no center labels,
an external center at `1` covering the target singleton `{0}`, and the
exact AC38 result with an arbitrary natural cardinality bound `N`, without
assuming `N>0`. The fully elaborated signatures were inspected for the
source/target radii, non-strict source and strict target errors, and omitted
geometric hypotheses. No admissions, new axioms, new PC imports, or edits
to existing mathematical files were used.
