# Proper pointed-limit uniqueness: MC24

The new leaf is
`DifferentialGeometry/Geometry/Metric/Approximation/PointedIsometry.lean`.
It contains three proved theorems, with no admissions. It uses the existing
pointed approximation calculus and the new `PointedGHConverges` predicate.
All underlying geometry here is abstract metric geometry; no PC manifold,
Riemannian, curvature or flow interface is involved.

## Exact statements

1. `exists_isometryEquiv_of_pointed_approximations`: let `(X,p)` and `(Y,q)`
   be **proper metric spaces** with chosen basepoints. Suppose sequences
   `R n`, `ε n` of real numbers satisfy `R n → +∞`, `ε n → 0`, and for
   every natural n there is a supplied actual
   `PointedBallApprox p q (R n) (ε n)`. Then there exists an isometry
   equivalence `e : X ≃ᵢ Y` with `e p = q`.
2. `exists_isometryEquiv_of_forall_pointed_approximation`: for the same
   proper pointed spaces, existence of such an approximation for every
   `0 < ε < R` suffices for the same pointed isometry conclusion.
3. `PointedGHConverges.exists_isometryEquiv`: if one sequence of pointed
   metric spaces `(Z n, o n)` converges in the declared pointed sense to
   both `(X,p)` and `(Y,q)`, and **both limits are proper**, there exists
   `e : X ≃ᵢ Y` with `e p = q`. This is the MC24 conclusion.

An isometry equivalence includes an actual bijection and exact preservation
of distance. The result is existence of a pointed isometry; it does not
claim that there is only one such function. The source spaces `Z n` need
not be proper, complete, geodesic or length spaces. Approximation maps need
not be continuous. No monotonicity of either radius or error sequence is
required in the first theorem. Its supplied approximation structures
already contain positivity and `ε n < R n` at every n.

`ProperSpace` means every closed metric ball is compact. In this metric
setting it implies completeness. In addition, the convergence predicate
already includes completeness of its target, as specified by the
blueprint. No conclusion about curvature, dimension, length closure or
geodesicity is asserted here. The stronger one-proper-limit version of
the source uniqueness theorem is not asserted.

## Proof and its boundary cases

For the first theorem, fix one ultrafilter U refining the natural-number
tail filter. Extend each approximation to X by assigning q outside its
source ball. This arbitrary extension is used only to give all maps a
common type. Every fixed x is eventually inside the genuine source ball,
because the radii tend to infinity.

The image of each fixed x eventually belongs to the compact ball centered
at q with radius `dist x p + 1`, by radial distortion and eventual
`ε n ≤ 1`. Along the **same U for every x**, compactness supplies a limit
F(x). Distortion tending to zero proves that F preserves every distance.
The exact basepoint condition on all approximations proves `F(p)=q`.

Surjectivity is proved separately; it is not inferred merely from distance
preservation. Given y, eventual coverage supplies actual source-ball points
z(n) with `dist y (f n (z n)) < ε n`. The radial estimate bounds these
preimages in the compact closed ball centered at p of radius
`dist y q + 2`. Properness of X therefore provides an ultrafilter limit x.
The estimate

```
dist y (F x) ≤ ε n + (dist (z n) x + ε n) + dist (f n x) (F x)
```

holds eventually. Every term on the right tends to zero along U. This
proves `F x = y`. It explicitly handles the moving preimages and never
assumes continuity or uniform convergence of the approximating maps.

The second theorem selects radii `R n = n+2` and errors `ε n = 1/(n+2)`.
The third theorem uses a common sufficiently late **same source member**
for the two approximations at radius `4(R+1)+4`, error `ε/20`. The existing
common-source comparison gives a map from X to Y on radius `R+1` with
error `ε/2`; buffered restriction gives radius R with error ε. Applying
the second theorem finishes the proof. No comparison of unrelated source
members is made, and no unsupported equal-radius restriction is used.

Chosen basepoints ensure that the two limit spaces and every source member
are nonempty. Singleton spaces and zero distances between equal points
are allowed. There is no hidden positive-diameter or positive-dimension
assumption.

## Blueprint and source record

The actual blueprint statement and full written proof were read in copied
revision207 `master207A.tex`, lines1615-1682,
`thm:metric-proper-limit-uniqueness`. The existing MC24 comparison record in
`metric_geometry_contracts.csv` and `reference_checks_revision68.md` was
also read. It identifies BBI8.1.7 and7.3.30 as the source background and
distinguishes the two-proper-limit project contract from the stronger
one-proper-limit source version. The archived BBI/author errata audit is
reused; no new exhaustive source or errata audit is claimed.

The formal proof uses an alternative compactness implementation: one
ultrafilter and compact balls replace the written proof's countable dense
set, subsequence diagonalization and dense extension. The statement and
the crucial bounded-coverage-preimage argument are retained. The existing
checked `Topology/MetricSpace/CompactApproximation.lean`, lines14-62, was
read as the compact-map precedent. Its theorem is not misapplied to
noncompact whole spaces. The new proof directly uses Mathlib compactness
of the actual proper-space closed balls.

Consequently the formal MC24 proof does not require first formalizing the
MC02 net enumeration or MC22 dense-domain extension route. This is a
proof-dependency improvement, not a change to those separate statements
or to the preserved historical blueprint text.

## Verification

`lake build DifferentialGeometry.Geometry.Metric.Approximation.PointedIsometry`
passed on Lean `v4.35.0-rc3` and Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`; Lake reported 1,691 jobs.
This was a targeted leaf build, not a whole-root/PC migration check.

All three theorem declarations were inspected with `#print axioms`; their
closures contain only `propext`, `Classical.choice`, `Quot.sound`.
There is no `sorryAx` or new mathematical axiom. The elaborated final
theorem type was also checked for its two properness hypotheses and its
single shared source sequence.
