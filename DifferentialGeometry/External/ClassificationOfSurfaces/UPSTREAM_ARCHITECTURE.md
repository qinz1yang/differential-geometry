# Architecture

This is the short human summary of the project. For the authoritative Lean declarations, read
`ClassificationOfSurfaces/API.lean`. For the theorem-by-theorem dependency graph and the
mathematical proof narrative, read `blueprint/src/content.tex`.

## Target

The Lean Eval theorem says that every compact connected Hausdorff topological 2-manifold with
boundary is homeomorphic to the sphere, an orientable normal-form quotient, or a non-orientable
normal-form quotient.

## Proof Structure

The completed topological route produces a faithful geometric triangulation. The classification
tail passes through exact finite cyclic boundary words and their computed polygonal realization:

```text
GeometricTriangulation
  → finite cyclic presentation
  → Gallier-Xu word normalization
  → polygonal realization
  → vendored Lean-Eval quotient
```

The combinatorial normalization and polygonal realization are separate proof layers. The final
theorem assembles their homeomorphisms with the geometric-triangulation realization
bridge.

## Completed Proof

The repository builds. On the triangulation side, the Moise/Radó chain is complete end-to-end for
compact connected Eval surfaces, including manifolds with boundary:

```lean
moise_triangulation :
  Nonempty (GeometricTriangulation S)
```

The relative polygonal replacement preserves the ambient boundary stratum exactly, and the
exposed-boundary-face invariant is carried through affine subdivision, common relabeling, and
gluing.  The former C0 chart-boundary hypothesis itself is discharged by planar no-retraction,
Brouwer's fixed-point theorem, and invariance of domain. Executable semantic anchors in
`Moise/Anchors.lean` and `Moise/Countermodels.lean` guard the definitions against vacuous
realizations.

The faithful polygonal quotient layer and the bottom API are complete:

- `EvalSurface` packages the Lean Eval hypotheses.
- `ChartBoundaryInvariant` is the low-level chart-extraction interface; its unconditional C0
  instance is proved in `Moise/BoundaryInvariant.lean`.
- `OrientedEdge` records oriented triangle sides.
- `FiniteSurfaceTriangulation` stores finite vertices, edges, triangles, oriented triangle boundary
  words, boundary-edge flags, and a homeomorphism from its realization to the target surface.
- `SurfaceCellComplex` stores finite faces, darts, vertices, source/target maps, inverse darts, and
  face boundary words.
- `SurfaceCellComplex.SignedDart` and `SurfaceCellComplex.oneFacePresentation` support concrete
  polygonal examples.
- `FiniteCyclicPresentation` packages finite cyclic signed face words. Its ordinary validity
  predicate retains nonempty face boundaries, while `IsGallierValid` adds exactly Gallier--Xu's
  exceptional one-face empty-word sphere. The book's P2-expanded two-monogon sphere is also
  available as an ordinary valid connected presentation.
- `FiniteCyclicPresentation.P1` implements the global oriented edge substitution, its exact
  contraction and cyclic-rotation reflection laws, and conditional preservation of ordinary
  validity, connectivity, and Gallier validity. The syntactic `P1Subdivision` relation closes
  canonical expansion under signed target isomorphism.
- `FiniteCyclicPresentation.P2` implements the cyclic oriented face split with possibly empty
  pieces, exact child-boundary and multiplicity laws, and preservation of ordinary validity,
  connectivity, and Gallier validity. Its exceptional empty-word sphere presentation regression
  is definitionally the two-monogon sphere presentation. `P2Subdivision` records genuine
  nondegenerate face cuts, plus that exceptional sphere conversion, up to signed presentation
  isomorphism of the target.
- `FiniteCyclicPresentation.Subdivides` closes P1/P2 steps transitively, and a common subdivision
  yields a faithful polygonal-realization equivalence. The generic Gallier--Xu Dyck rewrite is
  implemented by two explicit P2 cuts whose targets are signed-isomorphic.
- `FiniteCyclicPresentation.UnorientedPresentationIso` additionally permits independent reversal
  of face traversal, realized by reflection of the corresponding polygon disk when both endpoints
  are ordinary-valid. This comparison implements Gallier--Xu's generic cross-cap rewrite without
  conflating face reversal with signed edge relabeling.
- `FiniteCyclicPresentation.NormalizationEquivalent` is the validity-bundled equivalence closure
  used by derived normalization chains. Its primitive seams are common subdivisions and
  unoriented comparisons; every chain has a polygonal-realization homeomorphism. The generic Dyck
  and cross-cap rewrites are both registered in this closure.
- `FiniteCyclicPresentation.Handle.normalizationEquivalent` implements Gallier--Xu's three-Dyck
  handle extraction, and `LoopGrouping.normalizationEquivalent` implements the final block
  transport used to group boundary loops. The derived layer transports one-face validity across
  edge-occurrence permutations, so intermediate spellings do not leak proof obligations.
- `FiniteCyclicPresentation.HandleToCrosscaps.normalizationEquivalent` implements the complete
  four-rewrite Step 5 chain converting one crosscap plus one handle into three crosscaps, with an
  explicit final cyclic-order theorem.
- `PolygonCell` and `PolygonGluing` provide all-arity disk cells with circular indexed boundary
  arcs, generated side identifications, quotient topology, and quotient-congruence lemmas.
- `SurfaceCellComplex.BoundaryOccurrence`, `BoundaryPairing`, and `PolygonalRealization` provide
  an occurrence-indexed adapter to that quotient. Its pairing facts are derived from
  `IsSurfaceValid`, with nonempty face boundaries as the only polygon-specific extra condition.
  `mem_polygonalIdentifications_iff_exists_occurrences` exposes every compatible ordered pairing,
  and `oneFace_mem_polygonalIdentifications_iff` specializes it to two distinct finite positions
  in a one-face boundary word. Neither theorem chooses a unique matching.
- `FiniteSurfaceTriangulation.toCellComplex` preserves triangle faces, vertices, oriented edge
  darts, and oriented triangle boundary words; boundary status is then derived from occurrence
  multiplicity rather than copied from the triangulation's boundary flags.
- `FiniteSurfaceTriangulation.toFiniteCyclicPresentation` enumerates the finite faces and edges
  by `Fin`, preserves every cyclic signed boundary word, and transports certified validity and
  dual connectivity to the packed Gallier--Xu input. Consequently,
  `compact_eval_surface_has_valid_connected_finiteCyclicPresentation` connects the Eval surface
  hypotheses directly to the normal-form lane's finite combinatorial input.
- `GeometricTriangulation.polygonalRealizationHomeomorph` identifies that finite-cyclic polygonal
  quotient with the barycentric geometric realization. The compact Eval-surface specialization
  discharges the strong vertex-star certificate from the manifold charts.
- `FiniteCyclicPresentation.normalizeConnectedToCanonical` completes the validity-safe
  Gallier–Xu recursion, and `exists_admissible_normalForm_polygonallyEquivalent` exposes its exact
  canonical endpoint and polygonal-realization equivalence.
- Boundary-word examples for the disk, annulus, torus, projective plane, and Mobius strip have
  incidence- and occurrence-validity witnesses. The annulus now uses the length-six, two-contour
  word. These are combinatorial regression examples; the classification theorem uses the
  parametric canonical representatives below.
- `NormalForm.orientableBoundaryWord` and `.nonOrientableBoundaryWord` give the canonical
  parametric families matching the vendored Eval relations. Their lengths, edge multiplicities,
  incidence validity, connectivity, and admissible occurrence pairings are certified
  combinatorially. Forward maps and exact getters locate the entries
  of each named handle, crosscap, and boundary block. Every directed identification in either word
  is classified as the expected handle, crosscap, or boundary-seam pairing in either order, while
  singleton free-boundary sides are excluded.
- `RepresentativeCarrier.lean` identifies every one-face polygonal pre-realization with the exact
  vendored closed unit disk, computes its side coordinates, proves integral-period boundary
  invariance, and supplies closure-aware quotient congruence. `CanonicalCoordinates.lean` maps all
  five explicit pairing families into the trusted closures, including the reversed boundary
  indexing. `CanonicalGeneratorMaps.lean` maps arbitrary polygon generators and every trusted
  relation constructor into the opposite equivalence closure, yielding homeomorphisms between both
  canonical polygonal realizations and the exact Eval quotients.
- `FiniteCyclicPresentation.hasEvalRepresentative` composes normalization with the sphere,
  orientable, and nonorientable canonical realization homeomorphisms. `classification_of_surfaces`
  transports those endpoints across the geometric bridge to the input surface.

## File Map

- `ClassificationOfSurfaces/API.lean`: public API map and preferred code entry point.
- `ClassificationOfSurfaces/Surface.lean`: Eval hypothesis wrapper.
- `ClassificationOfSurfaces/Moise/`: the geometric triangulation theorem and its supporting
  polygonal/PL development.
- `ClassificationOfSurfaces/Triangulation.lean`: finite triangulation incidence package fed by
  the `GeometricTriangulation` bridge.
- `ClassificationOfSurfaces/CellComplex.lean`: shared finite surface cell-complex API.
- `ClassificationOfSurfaces/CanonicalWords.lean`: certified canonical normal-form words and
  one-face incidence presentations.
- `ClassificationOfSurfaces/CanonicalPairings.lean`: exhaustive pairing classifications for
  both canonical boundary-word families.
- `ClassificationOfSurfaces/CanonicalCoordinates.lean`: exact closed-disk coordinates and
  canonical-pairing-to-trusted-closure inclusions.
- `ClassificationOfSurfaces/CanonicalGeneratorMaps.lean`: bidirectional generator maps and
  canonical polygonal-realization homeomorphisms to the Eval quotients.
- `ClassificationOfSurfaces/RepresentativeCarrier.lean`: the exact one-face disk carrier,
  side-coordinate formulas, and raw/generated quotient bridges.
- `ClassificationOfSurfaces/SphereCarrierGeometry.lean`: compact disk carriers and the
  conjugation boundary identity used by the two-monogon sphere realization.
- `ClassificationOfSurfaces/SphereHemisphere.lean`: continuous upper/lower hemisphere maps,
  exhaustive sphere pairing classification, and the generator-compatible facewise pre-map.
- `ClassificationOfSurfaces/SphereQuotientHomeomorph.lean`: exact kernel relation, descended
  quotient map, and the homeomorphism from the two-monogon polygonal realization to the Eval
  sphere representative.
- `ClassificationOfSurfaces/SignedPresentation.lean`: inverse-dart orbits and lossless
  `Fin`-labelled signed boundary words.
- `ClassificationOfSurfaces/FiniteCyclicPresentation.lean`: packed cyclic face words, incidence
  predicates, non-mutating positive/negative face-orientation views, the exceptional empty-word
  sphere policy, and signed presentation isomorphisms with independent edge-orientation
  reversals.
- `ClassificationOfSurfaces/FiniteCyclicP1.lean`: exact Gallier--Xu P1 word substitution and
  contraction, canonical presentation expansion, edge/face bookkeeping, and preservation
  theorems.
- `ClassificationOfSurfaces/FiniteCyclicP2.lean`: exact Gallier--Xu P2 cyclic face cut,
  endpoint and orientation symmetries, dependent face/edge bookkeeping, connectivity path
  lifting, and ordinary/exceptional validity preservation.
- `ClassificationOfSurfaces/LeanEval/ChallengeDeps.lean`: the verbatim Lean-Eval disc carrier and
  quotient relations.
- `ClassificationOfSurfaces/LeanEval/RepresentativeSanity.lean`: project-owned radius and
  non-collapse checks for the vendored quotient representatives.
- `ClassificationOfSurfaces/Representatives.lean`: project-owned sphere abbreviation and
  normal-form indices; it does not redeclare the challenge relations.
- `ClassificationOfSurfaces/NormalForm.lean`: faithful finite-cyclic normal-form classification.
- `ClassificationOfSurfaces/EvalStatement.lean`: final Lean Eval theorem.
- `ClassificationOfSurfaces/LeanEval/SpecAudit.lean`: compile-time check that the public theorem
  has the exact Lean-Eval conclusion over the vendored constants.
- `ClassificationOfSurfaces/Examples.lean`: small regression examples.
