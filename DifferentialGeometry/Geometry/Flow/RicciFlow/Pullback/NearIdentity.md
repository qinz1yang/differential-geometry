# NearIdentity status

## Canonical API audit

The compact/global step already has the following Mathlib primitives, so this
file does not introduce a new covering or proper-map abstraction:

- `IsLocalDiffeomorph.isLocalHomeomorph` and
  `IsLocalHomeomorph.isLocallyInjective` provide the local topological layer;
- `IsLocalDiffeomorph.isOpen_range` provides openness of the image;
- `isCompact_range` plus `IsCompact.isClosed` provide closedness for a
  continuous map from a compact source to a Hausdorff target.  Equivalently,
  `Continuous.isProperMap` and `IsProperMap.isClosed_range` are available, but
  the compact-range route is shorter here;
- `lebesgue_number_lemma_nhds` and
  `comp_symm_mem_uniformity_sets` provide the uniform finite-cover argument;
- `isOpen_connectedComponent`, `IsClopen.connectedComponent_subset`, and
  `connectedComponent_eq` handle disconnected compact manifolds without an
  inadmissible `ConnectedSpace` assumption;
- once bijectivity is known,
  `IsLocalDiffeomorph.diffeomorphOfBijective` is the canonical final package.

No existing theorem was found that combines these APIs into the needed
near-identity self-map result.

## Source-written bricks

- `inj_of_unif_close`: for one fixed neighborhood cover on a compact uniform
  space, produces an entourage such that every map which is injective on each
  cover member and is that close to the identity is globally injective.  The
  cover is fixed before the map/family parameter is quantified, which is the
  uniformity required by the harmonic-map heat-flow application.
- `surj_of_unif_close`: produces a second entourage subordinate to connected
  components.  A near-identity map with clopen range is surjective, component
  by component; no connectedness of the whole manifold is assumed.
- `IsLocalDiffeomorph.clopen_range`: packages the canonical open-range and
  compact-closed-range facts for a compact Hausdorff self-manifold.
- `bij_of_unif_close`: intersects the injectivity and component entourages and
  packages the two conclusions as bijectivity.
- `eventually_bijective`: is the parameter-family consumer.  Uniform
  convergence to `id`, eventual injectivity on one fixed cover, and eventual
  clopen range imply eventual bijectivity.  This makes the quantifier order
  needed by the harmonic-map gauge explicit.

These theorems are source-written but intentionally not yet accepted as
proved: focused Lean verification is paused while the shared exported-artifact
chain is being restored.  No Lean or Lake command was run after drafting them.

## Remaining geometric input

The injectivity brick does not manufacture its fixed local cover.  The
harmonic-map heat-flow lane must first prove, from parametric `C1` closeness and
the manifold inverse-function theorem, that one finite family of source
neighborhoods is an injectivity cover for every sufficiently small time.  The
solution's `C0` closeness must then be small for the intersection of the
injectivity and connected-component entourages.  This is the honest bridge to
`IsLocalDiffeomorph.diffeomorphOfBijective`.
