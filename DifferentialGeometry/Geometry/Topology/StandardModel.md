# StandardModel

## Status

`StdModelCopy` and `stdModelCopy` are complete and focused verification passes
without `sorry`.

The constructor takes a boundaryless smooth manifold modeled by `I` and a
continuous linear equivalence from its model vector space to `F`.  It returns
the distinct same-universe type `ULift.{0} M`, equipped as a smooth manifold
over the standard model `𝓘(ℝ, F)`, together with the original T2,
sigma-compact, and boundaryless properties and a cross-model diffeomorphism
from `M`.

The carrier `Q` remains in the universe of `M`, while `F` now has its own
independent universe parameter.  This matches the already universe-polymorphic
private construction and permits, for example, an arbitrary-universe
three-manifold to be recharted over the small standard model
`EuclideanSpace ℝ (Fin 3)` without an unnecessary model-space `ULift`.

## Route

The original atlas is first recharted by the global homeomorphism obtained from
`I.Boundaryless` and the supplied continuous linear equivalence.  In
coordinates, the identity map is exactly the linear equivalence (and its
inverse), so its smoothness is proved without changing consumer assumptions.

The second transport uses the global homeomorphism
`Homeomorph.ulift : ULift.{0} M ≃ₜ M`.  Its singleton atlas is composed with
the standard atlas.  Compatibility follows from `HasGroupoid.comp` with the
identity-restriction groupoid; the resulting equivalence and its inverse have
identity coordinate expressions.

Using `ULift.{0}` rather than `Q = M` is essential: it keeps the copy in the
same universe while avoiding a same-type `ChartedSpace` instance diamond when
the original model is already standard.  No nonemptiness assumption is needed.

## Failed shapes

- Merely changing the vector model with
  `ModelWithCorners.transContinuousLinearEquiv` leaves the chart target `H`;
  it does not produce a manifold over the standard model space `F`.
- Casting a diffeomorphism across equality of whole `ChartedSpace` structures
  preserved the theorem type but made its underlying function opaque.  A
  direct identity-coordinate proof is both cheaper and more stable.

## Project accounting

- This generic same-universe standard-model-copy brick: 100%.
- The corresponding atlas/universe subproblem for `ham3_space_box`: 100%.
- `ham3_space_box` itself: not proved (0%); its dedicated topology/global
  geometry machinery is approximately 94%.
- The wider Hamilton positive-Ricci endpoint remains approximately 80%
  infrastructurally developed, while its still-open endpoint theorems must be
  counted separately.

The next consumer step is to use this package when the spherical quotient
producer needs a standard-model representative in the manifold's universe.
