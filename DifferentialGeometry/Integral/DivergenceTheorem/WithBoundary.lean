import Mathlib.Init

/-!
# Divergence theorem and integration by parts on manifolds with boundary

This module is the umbrella file for the with-boundary variant of the divergence
theorem and the associated integration-by-parts machinery on smooth Riemannian
manifolds whose model has a non-trivial boundary (i.e., where `[I.Boundaryless]`
is **not** assumed).

## Architecture

The boundaryless API in `DifferentialGeometry/Integral/DivergenceTheorem/`
(`LocalFormula.lean`, `ChartInvariance.lean`, `Closed.lean`, `Proper.lean`,
`IntegrationByParts.lean`, `Gradient.lean`, `Laplacian.lean`, `Green.lean`,
`Family.lean`) is preserved unchanged. The with-boundary variant is built as a
parallel, independent API under the present `WithBoundary/` sub-tree.

The two APIs agree on common ground (boundaryless manifolds, or sections /
functions whose support lies in the manifold interior). They diverge for inputs
that interact with the boundary, where the with-boundary API produces a
boundary integral term consistent with Stokes' theorem.

## Layered build-up

The sub-files are organised in successive layers, each independent of the
boundaryless API. The layers are loaded in order; later layers depend on
earlier ones.

### Interior-supported integration by parts

For an ambient manifold whose model `I` may have a boundary, but for inputs
whose support lies in `I.interior M`:

* `WithBoundary/PartialDerivWithin.lean` — Fréchet partial derivatives on the
  chart target, defined via `fderivWithin` (well-posed on a half-space target
  thanks to `uniqueDiffOn_extChartAt_target`).
* `WithBoundary/LocalFormula.lean` — chart-local Voss–Weyl divergence via
  within-derivatives; chart-invariance in the interior.
* `WithBoundary/Global.lean` — global divergence on the manifold, with
  Voss–Weyl identity on chart sources.
* `WithBoundary/POUReduction.lean` — Leibniz and POU sum identities.
* `WithBoundary/InteriorCompactSupport.lean` — divergence theorem and
  proper-support variant for sections supported strictly in `I.interior M`.
* `WithBoundary/InteriorIBP.lean` — integration by parts and Green's identities
  for inputs supported in `I.interior M`.

### Boundary as a manifold

Equips `boundary I M` with a smooth `(n-1)`-dimensional manifold structure when
the model `I` admits a smooth boundary, defines the induced Riemannian metric,
and constructs the surface measure.

* `WithBoundary/ModelBoundary.lean` — the abstract `HasSmoothBoundary I`
  typeclass.
* `WithBoundary/BoundaryManifold.lean` — `boundary I M` as a `ChartedSpace`
  and `IsManifold`.
* `WithBoundary/InducedMetric.lean` — pull-back of the ambient Riemannian metric
  to the boundary submanifold.
* `WithBoundary/SurfaceMeasure.lean` — Riemannian volume of the induced metric
  on the boundary.
* `WithBoundary/EuclideanHalfSpaceInstance.lean` — `EuclideanHalfSpace n` as a
  `HasSmoothBoundary` instance.

### Stokes' theorem and Green's identities

* `WithBoundary/OutwardNormal.lean` — outward unit normal vector field on the
  boundary, defined intrinsically via Riesz duality applied to a chart-local
  half-space-direction.
* `WithBoundary/Stokes.lean` — divergence theorem with boundary integral.
* `WithBoundary/GreenWithBoundary.lean` — Green's first and second identities
  with boundary terms.

### Time-dependent versions

* `WithBoundary/Family.lean` — pointwise-in-time wrappers and time-derivative
  identities for time-parameterised metric families.

## Out of scope

Manifolds with corners (e.g., `EuclideanQuadrant n`) are **not** handled by the
present API. The boundary of a corner-modelled manifold is a stratified space,
not a smooth submanifold, so the outward normal is not single-valued and
Stokes' theorem requires Whitney-style integration over strata. The
`HasSmoothBoundary` typeclass deliberately excludes corner models. A future
parallel tree (`WithBoundary/Corners/`) could host such an extension without
disturbing the present API.
-/
