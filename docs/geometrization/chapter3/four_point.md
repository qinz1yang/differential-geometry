# Four-point comparison and quadratic side comparison

## Implemented contract

`DifferentialGeometry/Geometry/Comparison/FourPoint.lean` uses namespace
`DifferentialGeometry.Geometry.Comparison.Toponogov` and the canonical comparison
angle API, through `ModelAngle.lean`.

`fourPointComparison κ s` means that for every center `x` and outer points
`a,b,c` in `s`, with each outer point different from `x`, the cyclic sum of the
three model angles `(a,b)`, `(b,c)`, `(c,a)` at `x` is at most `2π`.
Repeated outer points are allowed. In geometric applications `κ ≥ 0` is the
magnitude of the lower curvature bound `−κ`; that sign condition is a separate
hypothesis, not part of the predicate. At `κ = 0` the angle is exactly the
existing Euclidean comparison angle.

`fourPointComparison.mono` restricts this property to any subset.
`fourPointComparison_of_distinct` proves that, when `κ ≥ 0`, it is enough to
assume the displayed angle inequality for four distinct points. Thus the
repeated-outer-point convention does not strengthen the geometric source
contract. If two outer points agree, one angle is zero and each of the other
two is at most `π`; the proof covers all three possible outer coincidences.

`quadratic_side_comparison_of_fourPointComparison` assumes an arbitrary metric
space, a subset `s` with `fourPointComparison 0 s`, four points `a,b,z,v` in `s`,
and a real number `0 ≤ t ≤ 1` satisfying the actual distance identities

```
d(a,z) = t d(a,b),       d(z,b) = (1−t) d(a,b).
```

It proves

```
(1−t)d(v,a)² + t d(v,b)² − t(1−t)d(a,b)² ≤ d(v,z)².
```

This is the lower-curvature point-on-side inequality, with its lower-bound
direction and endpoint weights explicit. The two distance identities express
the needed placement of `z`; no geodesic existence or chosen parametrized
curve is assumed. There are no completeness, properness, local compactness,
dimension or smoothness hypotheses, and no dependence on PC manifold or
Ricci-flow interfaces. The canonical Euclidean angle leaf is reused unchanged.

## Proof and corner cases

The proof first treats `a=b`, `t=0`, `t=1`, and `v=z`. The constant side and
endpoint identities force the appropriate equality of points, so no positive
denominator assumption is used in those cases. In the remaining case, set
`α=d(z,a)`, `β=d(z,b)`, and `h=d(z,v)`; all three are positive and
`α+β=d(a,b)`. The angle between the arms to `a` and `b` equals `π`. Four-point
comparison bounds the sum of the other two angles by `π`, hence their cosines
have nonnegative sum. The actual metric cosine identities then give

```
β d(v,a)² + α d(v,b)² ≤ (α+β)h² + αβ(α+β).
```

Substitution and cancellation of the positive side length give the stated
inequality. All denominator clearing is confined to the positive case.
`v=a` and `v=b` remain permitted: the repeated-outer convention handles them.
The empty subset is harmless, since supplying the four membership hypotheses
already supplies the points needed by the conclusion.

## Source checks and scope

The existing checks in `reference_checks_revision69.md` and
`reference_checks_revision138.md` were read and reused for unchanged source
identity and comparisons. The exact blueprint passages read were AC37's final
zero-curvature algebra in `master207A.tex`, label
`thm:alexandrov-limit-nonnegative-comparison`, and ALS01 at label
`lem:alexandrov-global-four-point-side` (beginning at line 6731).

The archived Burago–Burago–Ivanov book was reopened at printed pages 352–353,
PDF pages 367–368: comparison-angle notation and Proposition 10.1.1, including
the proof passage applying the four-point inequality at a point on a side.
The source uses four distinct points; the new distinct-source adapter supplies
the precise convention translation. This implementation proves the required
zero-curvature cosine algebra directly rather than importing its planar
comparison lemma. Book SHA-256:
`4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`.

The retained author errata dated 2024-07-06 were reopened at PDF page 12. The
correction to the reverse-direction angle chain on printed page 353 does not
affect the forward implication proved here. Errata SHA-256:
`68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e`.
No new remote errata retrieval is claimed.

This file does not produce four-point comparison from a Riemannian curvature
bound, globalize a local comparison hypothesis, or assert an Alexandrov
structure theorem. It implements the final algebraic part of AC37 and the
point-on-side clause of ALS01. ALS01's separate arm-angle monotonicity clause
is not asserted to be implemented by this file.

## Independent model-angle review

The complete `ModelAngle.lean` proof bodies and their existing canonical
Euclidean-angle dependencies were independently read. No mathematical defect
was found. In particular:

- The hyperbolic formula uses `sqrt κ`, as required for curvature `−κ`.
- The regularized `sinh(x)/x` has its value `1` at zero justified by the
  derivative of `sinh`. The regularized quadratic `cosh` remainder comes from
  the exact double-angle identity, with value `1/2` at zero.
- The joint curvature-zero limit cancels the quadratic scale exactly; the
  limiting denominator is the product of the two strictly positive limiting
  central sides. Curvatures may equal zero infinitely often; eventual
  nonnegativity suffices. Continuity of `arccos` also covers endpoint angles.
- The genuine hyperbolic cosine identity assumes positive central sides and
  the two triangle inequalities and proves the cosine quotient belongs to
  `[-1,1]`. The analytic extension outside that domain is not mistaken for a
  geometric comparison theorem. Degenerate triangles with third side equal
  to the sum or absolute difference are explicitly covered.

## Verification

The scoped build
`lake build DifferentialGeometry.Geometry.Comparison.FourPoint` passed cleanly
under Lean 4.35.0-rc3 and mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e` (2,192 jobs).
`#print axioms` for the predicate and all three public theorems reported
exactly `propext`, `Classical.choice`, and `Quot.sound`. The independent
model-angle audit also checked that same axiom closure for the joint limit,
the positive-magnitude hyperbolic cosine identity, and the repeated-arm zero-angle
theorem. There are no admissions or new axioms in this file.

The subsequent ALS01–ALS05 development now supplies the angle-monotonicity
and actual global metric line-splitting consumers. See `line_splitting.md`.
The four-point producer boundary above remains unchanged.
