# MSM110 Chapter 6 Missing Definition Report

This report lists the vocabulary gaps that keep some Chapter 6 labels at
statement-scaffold or blocked status.  It is intentionally book-facing; the
canonical definitions should be added under `RicciFlower` when they become the
next proof target.

## Coordinate Evolution

- The regular-time mixed-Christoffel predicate now exists.  The deleted
  chart-local `eventually` route was the wrong surface.  The remaining
  derivation from spacetime smooth metric components should go through a
  pointwise coordinate-frame/Koszul producer and reuse
  `coordinateFrameAt_bracket_zero_of_mem`.
- The `partial Gamma + Gamma Gamma` curvature calculation is a coordinate-frame
  calculation.  Arbitrary-frame versions need structure coefficients or bracket
  terms.
- The pointwise volume-density evolution should be separated from the current
  integrated volume theorem.

## Curvature Operator Algebra

- Curvature-operator self-adjointness needs a finite-dimensional component
  algebra layer for the Riemann symmetries on `wedge^2`.
- The definitions of `Rm^2`, `Rm#`, and the `B_{ijkl}` algebra are present as
  statement surfaces, but their component identities still need a RicciFlower
  tensor-algebra proof.
- Positive/negative curvature-operator preservation needs a tensor maximum
  principle for invariant convex cones.

## Three-Dimensional Ricci Pinching

- The ordered eigenvalue vocabulary for the curvature operator and Ricci tensor
  should be made canonical, including ordering conventions for
  `lambda <= mu <= nu`.
- The diagonal curvature-operator ODE is recorded, but the route from the
  Uhlenbeck evolution equation to the ordered eigenvalue system still needs the
  finite-dimensional spectral bridge.
- Ricci positivity preservation should be phrased as an invariant cone theorem,
  not as an ad hoc scalar inequality.

## Gradient and Long-Time Estimates

- The scalar-gradient section needs Bochner-type evolution formulas for
  `|grad R|^2`, `|Ric|^2`, and the quotient quantities used in Hamilton's
  estimate.
- The higher derivative estimates currently reference the Chapter 5 BBS
  estimates as an intentional interface.  A future discharge needs a canonical
  BBS theorem and a continuation theorem for Ricci flow.
- Global maximal-time vocabulary should distinguish finite maximal interval,
  extendability, curvature blowup, and singularity model.

## Normalized Flow and Convergence

- Normalized-flow statements need a canonical volume-normalizing time change,
  scalar normalization factor, and relation between unnormalized and normalized
  curvature components.
- The `BoundR-bar` chain needs Myers diameter comparison, volume comparison,
  and positive Ricci pinching in the normalized setting.
- Exponential convergence needs a precise Einstein-limit object, metric
  convergence norms, and derivative estimates strong enough to upgrade
  pointwise pinching to smooth convergence.
