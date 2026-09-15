# ClassificationOfSurfaces vendor record

## Provenance

Source: [mccorvie/classification-of-surfaces](https://github.com/mccorvie/classification-of-surfaces),
commit `e3c7230fe78d7b056a415d9ecae6f77887046b32` (Ryan McCorvie, 2026-08-28).
Imported on 2026-09-14. License: Apache-2.0; the full upstream license is copied verbatim to `LICENSE`.
Source copyright and author headers, comments, module documentation, citation metadata, and
`LeanEval.Topology.ClassificationOfSurfaces` namespaces are retained. The original project
README and architecture document are copied verbatim as `UPSTREAM_README.md` and
`UPSTREAM_ARCHITECTURE.md`.

Upstream uses Lean 4.32.0 and Mathlib `81a5d25`; this checkout uses Lean 4.33.1 and its
configured Mathlib revision. Native bridges live outside this vendor directory.

## First batch and dependency order

The batch is the complete local import closure of `Moise/PolygonalSchoenflies.lean`.
Its source covers finite planar complexes, subdivision, supported triangle moves,
polygonal Jordan separation, and polygonal Schoenflies. The original source labels
`closedRegion_is_polyhedron` as Moise Chapter 2 Theorem 2,
`polygonal_schoenflies_rel` as Chapter 3 Theorem 7, and `polygonal_schoenflies`
as Chapter 3 Theorem 5. The consumer plan's Chapter 3 Theorem 6 and Chapter 5
Theorem 3 formulations require the native PL bridge; source labels alone do not
certify those stronger consumer statements.

| Module | Upstream lines | Local dependencies |
|---|---:|---|
| `GeometricTriangulation` | 694 | Mathlib only |
| `PlaneComplex` | 1360 | `GeometricTriangulation` |
| `AmbientHomeomorph` | 262 | `PlaneComplex` |
| `LineSubdivision` | 3984 | `PlaneComplex` |
| `ElementaryMove` | 1078 | `AmbientHomeomorph`; `LineSubdivision` |
| `FreeTriangle` | 1738 | `ElementaryMove` |
| `CommonSubdivision` | 976 | `FreeTriangle` |
| `ThinKiteMove` | 1316 | `ElementaryMove` |
| `FreeTriangleMove` | 1155 | `FreeTriangle`; `ThinKiteMove` |
| `ConeExtension` | 1377 | `FreeTriangleMove` |
| `FinitePLHomeomorph` | 539 | `CommonSubdivision`; `ConeExtension` |
| `PLMoves` | 532 | `FinitePLHomeomorph`; `ConeExtension`; `FreeTriangleMove` |
| `PolygonalJordan` | 4158 | `PlaneComplex` |
| `PolygonalPolyhedron` | 429 | `LineSubdivision`; `PolygonalJordan` |
| `PolygonalCrosscut` | 2865 | `PolygonalPolyhedron`; `FreeTriangle` |
| `PolygonalSchoenflies` | 3023 | `PLMoves`; `PolygonalPolyhedron`; `PolygonalCrosscut` |

## Local source modifications

The line numbers below refer to the pinned upstream files. Import names alone are
rewritten in this initial copy; all subsequent API corrections are recorded below
under the affected file. No source definitions, assumptions, comments, or namespaces
are removed by the import rewrite.

### `Moise/GeometricTriangulation.lean`

- No local source changes.

### `Moise/PlaneComplex.lean`

- Upstream lines 694-704, `mapAffineEquiv_support`: make the unchanged vertex indexing explicit with `change`, then use the carrier image equality and `Set.image_iUnion`. Lean 4.33 no longer rewrites this dependent index reliably after simplifying the transported complex fields.
- Upstream lines 1042-1051, `Subdivides.mapAffineEquiv`: apply the same carrier equalities with `Eq.trans_le` and `Set.image_mono` instead of rewriting semireducible transported vertex types.
- Upstream lines 1166-1183, `IsPLOn.affineConjugate`: explicitly transport membership through `mapAffineEquiv_cellCarrier` before extracting its image witness, for the same dependent-type elaboration change.
- Line 12: `import ClassificationOfSurfaces.Moise.GeometricTriangulation` becomes `import External.ClassificationOfSurfaces.Moise.GeometricTriangulation`.

### `Moise/AmbientHomeomorph.lean`

- Upstream lines 64-65, `repositionHomeomorph_apply_realization`: apply `congrArg` to `Homeomorph.symm_apply_apply` to reduce the composite on its realization; the old broad `simp` followed by `rfl` leaves a non-definitional inverse identity in Lean 4.33.
- Upstream lines 155 and 162: replace deprecated `continuousOn_iff_continuous_restrict` by `continuousOn_iff_continuous_domRestrict`.
- Upstream lines 160 and 167: remove the deprecated and unused `Set.restrict` simplifier argument; the remaining function and subtype facts prove the same equality.
- Line 6: `import ClassificationOfSurfaces.Moise.PlaneComplex` becomes `import External.ClassificationOfSurfaces.Moise.PlaneComplex`.

### `Moise/LineSubdivision.lean`

- Upstream lines 1416, 1448, 1537, 1563, 1673, 1697, and 1780: replace `rw` by `erw` for `TriangleMesh.reindex_support`, allowing the unchanged semireducible vertex types of the mesh constructors to unfold.
- Upstream lines 2039-2042 and 2049-2051: finish the simplified triangle-pattern equalities with `rfl`, reducing the embedding structure coercions left by Lean 4.33.
- Upstream lines 2530, 2542, 2553, 2609, 2689, and 2741: expand `split_ifs` into the same four ordered `by_cases` decisions and explicit `erw [dif_pos ...]` / `erw [dif_neg ...]`. The branch proofs are unchanged; the old implicit-transparency simplifier cannot reduce dependent triangle sets to the common refined vertex type.
- Line 6: `import ClassificationOfSurfaces.Moise.PlaneComplex` becomes `import External.ClassificationOfSurfaces.Moise.PlaneComplex`.

### `Moise/ElementaryMove.lean`

- Upstream line 962: use the explicit `Homeomorph.symm_apply_apply x` proof after rewriting the center realization, avoiding the implicit-transparency simplifier on its vertex type.
- Upstream lines 953 and 1050: use `erw` for the support/ambient repositioning formulas, unfolding the unchanged semireducible fan vertex type.
- Upstream lines 1001-1002: use `exact congrArg Subtype.val he` instead of `simpa only` to identify the realization value with the same barycentric evaluation under default transparency.
- Line 6: `import ClassificationOfSurfaces.Moise.AmbientHomeomorph` becomes `import External.ClassificationOfSurfaces.Moise.AmbientHomeomorph`.
- Line 7: `import ClassificationOfSurfaces.Moise.LineSubdivision` becomes `import External.ClassificationOfSurfaces.Moise.LineSubdivision`.

### `Moise/FreeTriangle.lean`

- Line 6: `import ClassificationOfSurfaces.Moise.ElementaryMove` becomes `import External.ClassificationOfSurfaces.Moise.ElementaryMove`.

### `Moise/CommonSubdivision.lean`

- Upstream line 227: use `erw` for `Finset.sum_coe_sort` in `baryEval_triangleCoords`, allowing the mesh-to-complex vertex type to unfold while reindexing the unchanged sum.
- Line 6: `import ClassificationOfSurfaces.Moise.FreeTriangle` becomes `import External.ClassificationOfSurfaces.Moise.FreeTriangle`.

### `Moise/ThinKiteMove.lean`

- Upstream lines 887 and 955: use `erw` to unfold the ambient fan repositioning formula on the left and right spokes; the fan vertex type needs default transparency in Lean 4.33.
- Line 6: `import ClassificationOfSurfaces.Moise.ElementaryMove` becomes `import External.ClassificationOfSurfaces.Moise.ElementaryMove`.

### `Moise/FreeTriangleMove.lean`

- Line 6: `import ClassificationOfSurfaces.Moise.FreeTriangle` becomes `import External.ClassificationOfSurfaces.Moise.FreeTriangle`.
- Line 7: `import ClassificationOfSurfaces.Moise.ThinKiteMove` becomes `import External.ClassificationOfSurfaces.Moise.ThinKiteMove`.

### `Moise/ConeExtension.lean`

- Upstream line 30: disambiguate the topology notation scope as `_root_.Topology`.
- Upstream lines 455 and 606: transport membership with the explicit active/used carrier equality instead of the implicit-transparency simplifier.
- Upstream lines 533 and 684: compose the same active/used carrier equality with the face containment rather than simplifying it.
- Upstream line 735: explicitly apply `congrArg q (e.symm_apply_apply i)` after reducing the prescribed-value conditional, retaining the same affine extension.
- Upstream line 996: supply `K.vertexDecidableEq` to `Fintype.sum_ite_eq'`, matching the decidable equality instance in the repositioned mesh sum.
- Line 6: `import ClassificationOfSurfaces.Moise.FreeTriangleMove` becomes `import External.ClassificationOfSurfaces.Moise.FreeTriangleMove`.

### `Moise/FinitePLHomeomorph.lean`

- Line 6: `import ClassificationOfSurfaces.Moise.CommonSubdivision` becomes `import External.ClassificationOfSurfaces.Moise.CommonSubdivision`.
- Line 7: `import ClassificationOfSurfaces.Moise.ConeExtension` becomes `import External.ClassificationOfSurfaces.Moise.ConeExtension`.

### `Moise/PLMoves.lean`

- Line 6: `import ClassificationOfSurfaces.Moise.FinitePLHomeomorph` becomes `import External.ClassificationOfSurfaces.Moise.FinitePLHomeomorph`.
- Line 7: `import ClassificationOfSurfaces.Moise.ConeExtension` becomes `import External.ClassificationOfSurfaces.Moise.ConeExtension`.
- Line 8: `import ClassificationOfSurfaces.Moise.FreeTriangleMove` becomes `import External.ClassificationOfSurfaces.Moise.FreeTriangleMove`.

### `Moise/PolygonalJordan.lean`

- Upstream lines 142 and 202: apply the unchanged edge-image equality directly; this unfolds the transported polygon's size and vertex function under default transparency.
- Upstream lines 109 and 173: normalize the successor index with `simpa only [add_assoc, one_add_one_eq_two]`, replacing `convert ...; ring` and its avoidable tactic suggestions.
- Upstream lines 726, 731, 1138, 1154, 1398, and 1646-1648: use `simpa` with the corresponding outgoing/incoming vector definition to normalize the segment endpoint, avoiding `convert ...; abel` suggestions.
- Upstream lines 733-734: explicitly prove the same cyclic-index arithmetic equality before simplifying the adjacent-edge intersection.
- Upstream line 2022: replace deprecated `Set.mem_setOf_eq` by `Set.mem_ofPred_eq`.
- Line 6: `import ClassificationOfSurfaces.Moise.PlaneComplex` becomes `import External.ClassificationOfSurfaces.Moise.PlaneComplex`.

### `Moise/PolygonalPolyhedron.lean`

- Line 6: `import ClassificationOfSurfaces.Moise.LineSubdivision` becomes `import External.ClassificationOfSurfaces.Moise.LineSubdivision`.
- Line 7: `import ClassificationOfSurfaces.Moise.PolygonalJordan` becomes `import External.ClassificationOfSurfaces.Moise.PolygonalJordan`.

### `Moise/PolygonalCrosscut.lean`

- Upstream lines 668-670 and 688: expose the inserted polygon's edge-index type with `change` before simplifying union membership. Remove the three now-redundant `change` steps at upstream lines 700, 703, and 710.
- Upstream lines 720, 722, and 732: normalize cyclic addition with `simpa only [add_right_comm]` rather than `convert ...; ring`, eliminating avoidable tactic suggestions.
- Upstream lines 742-745: expose the rotated edge endpoints and rewrite the same associativity/commutativity equality directly.
- Upstream lines 751-761: prove carrier invariance by `Set.iUnion_congr` and the surjective additive reindexing, avoiding dependent-union simplification.
- Upstream lines 1066 and 1069: use `erw` for the rotated edge formula.
- Upstream line 1904: explicitly rewrite the cyclic successor index with `add_right_comm`, replacing `abel` on an iff and its tactic suggestion.
- Upstream lines 1915 and 1930: use `erw` for the crossing predicate on the cut circle, unfolding its size.
- Upstream line 2805: use `erw` for disjoint triangle membership, identifying the two side meshes' common vertex type.
- Line 6: `import ClassificationOfSurfaces.Moise.PolygonalPolyhedron` becomes `import External.ClassificationOfSurfaces.Moise.PolygonalPolyhedron`.
- Line 7: `import ClassificationOfSurfaces.Moise.FreeTriangle` becomes `import External.ClassificationOfSurfaces.Moise.FreeTriangle`.

### `Moise/PolygonalSchoenflies.lean`

- Upstream lines 196 and 208: normalize successor addition with `simpa only [add_assoc, one_add_one_eq_two]`, replacing `convert ...; ring` and its tactic suggestions.
- Upstream line 2185: use `erw` for boundary-edge membership on the side mesh's unchanged vertex type.
- Upstream line 3012: expose the composite homeomorphism as its pointwise lambda with `change`; the old `simp only [Homeomorph.trans_apply]` makes no progress inside the image expression in Lean 4.33.
- Line 6: `import ClassificationOfSurfaces.Moise.PLMoves` becomes `import External.ClassificationOfSurfaces.Moise.PLMoves`.
- Line 7: `import ClassificationOfSurfaces.Moise.PolygonalPolyhedron` becomes `import External.ClassificationOfSurfaces.Moise.PolygonalPolyhedron`.
- Line 8: `import ClassificationOfSurfaces.Moise.PolygonalCrosscut` becomes `import External.ClassificationOfSurfaces.Moise.PolygonalCrosscut`.

## Build configuration

The project `lakefile.toml` declares `lean_lib External` so these modules can be
built by their module names during later integration. This lane uses only its
`check-f.ps1` and `audit-f.ps1` focused scripts and does not register the modules
in `DifferentialGeometry.lean` or run `lake build`.

## Verification

All 16 modules were checked in the dependency order above with this lane's
`check-f.ps1`; every check exited 0. `AuditS1.lean`, run with `audit-f.ps1`,
also exited 0. The six audited declarations below each depend only on
`propext`, `Classical.choice`, and `Quot.sound`:

- `LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.polygonal_schoenflies_rel`
- `LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.polygonal_schoenflies`
- `LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.closedRegion_is_polyhedron`
- `LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.frontier_interiorRegion`
- `LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle.frontier_closedRegion`
- `LeanEval.Topology.ClassificationOfSurfaces.Moise.FinitePLHomeomorphOn.symm`

| Module | Check exit | Retained style warnings |
|---|---:|---:|
| `GeometricTriangulation` | 0 | 3 |
| `PlaneComplex` | 0 | 0 |
| `AmbientHomeomorph` | 0 | 0 |
| `LineSubdivision` | 0 | 0 |
| `ElementaryMove` | 0 | 0 |
| `FreeTriangle` | 0 | 0 |
| `CommonSubdivision` | 0 | 0 |
| `ThinKiteMove` | 0 | 0 |
| `FreeTriangleMove` | 0 | 0 |
| `ConeExtension` | 0 | 1 |
| `FinitePLHomeomorph` | 0 | 0 |
| `PLMoves` | 0 | 0 |
| `PolygonalJordan` | 0 | 1 |
| `PolygonalPolyhedron` | 0 | 0 |
| `PolygonalCrosscut` | 0 | 7 |
| `PolygonalSchoenflies` | 0 | 1 |

The following original proof-style warnings are retained under the explicit vendor
exception in `HANDOFF_CODEX_S.md` section 1. There are no other warnings or
standalone tactic suggestions in the final logs.

- `GeometricTriangulation.lean`: local line 571, upstream line 571, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `GeometricTriangulation.lean`: local line 572, upstream line 572, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `GeometricTriangulation.lean`: local line 610, upstream line 610, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `ConeExtension.lean`: local line 1014, upstream line 1013, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `PolygonalJordan.lean`: local line 228, upstream line 230, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `PolygonalCrosscut.lean`: local line 418, upstream line 418, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `PolygonalCrosscut.lean`: local line 1170, upstream line 1180, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `PolygonalCrosscut.lean`: local line 1213, upstream line 1223, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `PolygonalCrosscut.lean`: local line 1248, upstream line 1258, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `PolygonalCrosscut.lean`: local line 1346, upstream line 1356, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `PolygonalCrosscut.lean`: local line 1396, upstream line 1406, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `PolygonalCrosscut.lean`: local line 1690, upstream line 1700, `linter.style.haveILetI` on the unchanged `letI` in a proof.
- `PolygonalSchoenflies.lean`: local line 787, upstream line 787, `linter.style.haveILetI` on the unchanged `letI` in a proof.

The local source diff against the pinned upstream was reviewed after import
normalization. All comment blocks and declaration names are retained; changes are
limited to the logged import/elaboration fixes. No proof placeholders, axioms,
linter suppressions, or resource options were added. License, upstream README, and
upstream architecture copies are byte-identical to the supplied originals.

The upstream ambient relative theorem certifies PL behavior on the closed polygonal
region. Its public statement does not certify PL behavior on the whole plane.
The stronger relative endpoint is proved by the native adaptation described below.

## Native planar PL bridge

`DifferentialGeometry/Topology/PiecewiseLinear/PlanarSchoenflies.lean` adapts the
pinned upstream mathematics to the native `IsPiecewiseAffineOn`,
`IsPLHomeomorphOn`, `IsPLSphere`, and `IsPLBall` predicates. The native file follows
the owner's zero-comment source rule; attribution and the Apache-2.0 license are
recorded here and in `LICENSE`.

- The two directions between finite planar PL certificates use a new conversion
  from native finite geometric simplicial complexes to `PlaneComplex`. The
  conversion preserves the exact support and simplex carriers.
- The private refinement and edge-containment proofs and
  `exists_polygonalCircle_image_of_isPLOnSet` adapt four proofs from upstream
  `ClassificationOfSurfaces/Moise/PLApproximation.lean`, lines 400–597:
  `PolygonalCircle.exists_refinement_containing_complex_vertices`,
  `PlaneComplex.exists_face_containing_polygon_edge`,
  `PolygonalCircle.exists_mapEmbedding_of_affineOn_complex`, and
  `PolygonalCircle.exists_image_of_isPLOnSet_embedding`.
  They are moved into the native namespace, given native names and local classical
  scopes, and the active-complex carrier rewrite is made explicit for Lean 4.33.
  Their hypotheses and mathematical proofs are unchanged. These proofs use only
  the first batch of vendor modules; `PLApproximation` itself is not imported.
- `polygonalCircleOfAffineIndependentTriple` generalizes the triangular example
  in upstream `ClassificationOfSurfaces/Moise/Anchors.lean`, lines 65–102,
  from the fixed standard vertices to any affinely independent triple.
- Native simplex-frontier and sphere-boundary lemmas in `SimplexFrontier.lean`
  identify the full-dimensional convex-hull frontier with its proper faces using
  barycentric coordinates. They use the native PL simplex-boundary API and
  Mathlib affine-basis results.
- `isPLBall_of_isPLSphere_one` proves the full P.1 consumer statement, with a
  bounded PL 2-ball filling every native planar PL 1-sphere. Both conversions
  between polygon carriers and native PL 1-spheres are proved.
- `exists_isPLHomeomorphOn_straighten` and
  `exists_isPLHomeomorphOn_straighten_of_isPLSphere_one` certify PL behavior in both
  directions on the entire plane and identity outside the prescribed open set.
  The earlier `_on_closedRegion` signatures are preserved as corollaries.
- The two native free-triangle removal proofs adapt upstream
  `PolygonalSchoenflies.lean`, lines 2514–2712 and 2716–2900, respectively:
  `PolygonalCircle.TriangleMesh.exists_supported_polygonalDisk_move_of_oneEdgeFree`
  and `PolygonalCircle.TriangleMesh.exists_supported_polygonalDisk_move_of_twoEdgeFree`.
  The geometric arguments and supported thin-kite witnesses are unchanged.
  The final `FinitePLHomeomorphOn` certificate on the mesh support is strengthened
  to native `IsPLHomeomorphOn` on the entire plane, using the finite-PL certificate
  on the kite patch and its identity behavior on the complement. Names and
  namespace are native; comments are omitted under the owner's native source rule.
- The native global straightening induction adapts upstream
  `PolygonalSchoenflies.lean`, lines 2928–2997. It composes the stronger ambient
  certificates directly instead of using `PLAmbientShellingIn`, which retains
  only PL behavior on the disk. The same geometric-ear induction, polygonal disks,
  triangle target, and support condition are preserved.
- The two `univ_of_eqOn_compl` lemmas in native `AmbientExtension.lean` use the
  project's relative PL extension API and continuity to glue a map that is PL
  on a finite polyhedron and the identity off it. They do not copy upstream code.

The second vendor batch has not been imported: its approximation headlines are
finite-complex embedding approximations (Moise 6.2–6.3), and do not by themselves
supply the ambient, supported, control-function conclusion of P.4 (10.8).

`SimplexFrontier` and `PlanarSchoenflies` both pass the lane's standard-linter
focused check with exit 0 and zero warnings. `AuditS2.lean` audits 14 bridge and
headline declarations; every closure contains only `propext`, `Classical.choice`,
and `Quot.sound`, and the audit exits 0.

## Additional consumer audit and second-batch gate

`AuditS5.lean` audits the stronger geometric-ear theorem
`TriangleMesh.exists_two_geometricallyFreeTriangles_of_polygonalDisk` and the three
`PolygonalTheta` declarations `disjoint_interior13_interior23`,
`closedRegion13_inter_closedRegion23`, and `closedRegion_eq_union`. All four
closures contain only `propext`, `Classical.choice`, and `Quot.sound`; audit exit 0.
The geometric-ear theorem certifies the triangulated polygonal-disk case of P.3,
not the general cell-decomposition or relative-subdisk forms of Moise 17.2–17.3.
The theta results certify polygonal separation, not arbitrary-arc Theorem 4.4 or
Problem 4.1. No second-batch module is imported: its finite-complex embedding
approximation and polygon-family subdivision statements do not close P.4 or the
remaining P.5 obligations. This audit changes no vendor Lean source.

The later native `BallFrontier`, `PushProperty`, `AmbientExtension`, `ConeIsotopy`,
`SimplexBoundaryImage`, and `SimplexPush` developments use the project's native
PL and simplicial APIs. Their initial proofs do not copy additional upstream Lean proofs.
Their source is not subject to the vendor style exception. In particular, the
Moise 17.4 tetrahedral-face push uses relative PL extension and cone-apex motion;
it neither assumes global PL behavior of the upstream relative Schoenflies map
nor imports the second batch. Moise 17.5, 17.6, and 17.8 remain open in this lane.

The final combined `AuditS9.lean` imports the planar bridge, boundary/frontier
modules, and the tetrahedral push chain in one environment. Its 50 distinct
declarations all have only the three standard foundational axioms; audit exit 0.
All 11 changed native modules pass their final focused checks with zero warnings.

After closing the full planar relative theorem, the updated `AmbientExtension`
and `PlanarSchoenflies` checks both exit 0 with zero warnings. `AuditS10.lean`
checks the seven new declarations, both compatible closed-region corollaries,
and the tetrahedral-face push in a single environment: all ten closures contain
only `propext`, `Classical.choice`, and `Quot.sound`, audit exit 0. No vendor Lean
source changes or second-batch imports are needed for this strengthening.

## Native extension over two cones

`AmbientExtension.IsPLHomeomorphOn.exists_extension_of_eqOn_frontier` generalizes
the identity-pasting construction in upstream `AmbientHomeomorph.lean`, lines
133–197. The new theorem applies to finite polyhedra in arbitrary finite-dimensional
real normed spaces and starts with a native PL self-map. It uses the native
setwise inverse and proves the global PL certificate via `univ_of_eqOn_compl`;
it does not introduce a planar subtype-homeomorphism definition or copy the
upstream declaration. The frontier-fixing assumption is retained explicitly.

The new `PLHomeomorphGluing` and `ConeAmbientExtension` proofs are native.
They glue two PL self-maps that agree on and preserve their intersection, then
extend the cone maps by identity. The cone theorem requires the geometric
intersection and frontier conditions explicitly. It does not establish those
conditions for every tetrahedral boundary star, and does not claim Moise 17.5.
All three affected modules pass focused checks with exit 0 and zero warnings.
`AuditS11.lean` checks the three new declarations together with the full planar
relative theorem; all four closures contain only the three standard axioms,
audit exit 0.

Final verification after the F synchronization through `b66f6b5b0`: all 13 native
S modules and the two synchronized F half-space modules pass the focused checks,
exit 0 with zero warnings. `AuditS12.lean` imports the complete S chain together
and checks 60 distinct declarations; every axiom closure contains only the three
standard axioms, audit exit 0. Logs: `.lake/scratch/final2-*.log` and
`.lake/scratch/audit-final2-s.log` in the S worktree.


## Prescribed terminal triangle

The native `PlanarSchoenflies.exists_isPLHomeomorphOn_straighten_to_triangle`
strengthens the existing supported shelling: the terminal triangle is any
specified triangle of the initial disk triangulation. At each nontrivial step,
`TriangleMesh.exists_two_geometricallyFreeTriangles_of_polygonalDisk`
(upstream `PolygonalSchoenflies.lean`, lines 2322 onward) supplies two distinct
geometrically free triangles, so one can be deleted without deleting the
specified triangle. The original native straightening theorem is now a
corollary, with its public signature unchanged. This strengthens the
triangulated-disk input for Moise 17.5; it does not assert the full relative
subdisk form of 17.3 or the tetrahedral conclusion of 17.5. No vendor Lean
source is modified.

The focused `PlanarSchoenflies` check exits 0 with zero warnings. `AuditS13.lean`
audits the prescribed-triangle endpoint and both ambient straightening
headlines; all three closures contain only the standard foundational axioms,
and the audit exits 0.


## Two-sided cones at simplex vertices

The new native `ConeHalfSpace` and `SimplexCorner` modules do not copy additional
vendor source. They use affine supporting functions to construct the interior
and exterior cone apices described in Moise 17.5. The construction works for
any affine-independent simplex with at least two vertices, in a finite-dimensional
real normed space. The apices can be arbitrarily close to the chosen vertex;
both cones lie in any prescribed open neighborhood of the simplex. Their
intersection is exactly the vertex star, the interior cone lies in the simplex,
and the exterior cone meets the simplex exactly in that star. The vertex star
is identified with `simplexAvoiding T hT {T.erase a}`; its intersection with the
opposite facet is the boundary of that facet. The interior cone together with
the remaining simplex fills the original simplex.

These results discharge the existence, support, and intersection inputs for
the proposed two-cone extension. The frontier inclusion in
`exists_isPLHomeomorphOn_extension_coneComplex_union` and the application of
local moves to a triangulated disk in the tetrahedral boundary remain to be
proved; this checkpoint does not close Moise 17.5. Both new modules pass the
focused check with exit 0 and zero warnings. `AuditS14.lean` checks all eleven
new declarations, with exit 0 and only the three standard foundational axioms.


## Ambient extension of a simplex vertex star

The native `ConeIntersection`, `SimplexCornerFrontier`, and
`SimplexCornerExtension` modules complete the geometric input for extending a
PL self-map of a simplex vertex star. The apex construction in `SimplexCorner`
now also certifies the outer simplex and that the original vertex lies in its
open simplex. The two existing existential signatures are strengthened with
these two conclusions, and their in-tree consumer is updated.

The frontier argument decomposes the outer simplex into the original simplex
and the exterior cone, and the original simplex into the interior cone and
an inner simplex. Cone intersection formulas identify the common side faces;
the frontier of the union lies in the cones over the boundary of the opposite
facet. Applying the earlier two-cone extension therefore introduces no
unproved geometric hypotheses. The endpoint
`exists_isPLHomeomorphOn_extension_simplex_vertex_star` extends every PL
self-map of the vertex star that fixes that boundary, preserves the original
simplex, and fixes the complement of any prescribed open neighborhood of it.
The argument applies in every positive dimension when the simplex spans its
ambient finite-dimensional real normed space.

These are native proofs; no vendor Lean source is changed. The geometric
paragraph of Moise 17.5 is now implemented. The remaining theorem needs local
free-triangle deletion on an adapted triangulation of a disk in the tetrahedral
boundary, followed by the retained-triangle induction. The new endpoint alone
does not identify every such disk with a tetrahedral facet, and does not close
17.5, 17.6, or 17.8. All four affected modules pass focused checks with exit 0
and zero warnings. `AuditS15.lean` audits eighteen declarations including the
new geometric chain, the planar prescribed-triangle theorem, and the existing
17.4/17.7 endpoints; every closure contains only the three standard axioms,
audit exit 0.

## Vertex-star coordinates and adapted subdivisions

The native `SimplexCornerChart` module identifies a simplex vertex star with
its opposite facet by the simplicial map that sends the distinguished vertex
to the facet centroid and fixes all remaining vertices. This map is affine on
each original face, is a PL homeomorphism, and fixes the facet boundary.
Conjugating a boundary-fixing PL self-map of the facet through these coordinates
now produces an ambient PL homeomorphism preserving the full simplex and
fixing the complement of its prescribed open neighborhood.

`Mesh` now supplies subdivisions whose entire union of vertex closed stars
for each face lies in one member of a relative open cover. This lemma works
in arbitrary real normed spaces. `Subcomplex` preserves any finite family of
polyhedra while making that subdivision, and `StarSubdivision` specializes
the cover to the original vertex open stars. Applied to the tetrahedral
boundary and the given disk, it supplies the adapted triangulation needed in
Moise 17.5. The earlier chart-cover theorem in `Combinatorial` now uses the
general lemma and no longer requires its source space to be finite-dimensional.

No vendor Lean source is modified. Five affected modules and both existing
consumers of the generalized chart-cover theorem pass focused checks with
exit 0 and zero warnings. One consumer check initially encountered shared
artifacts from the E3 branch, which places `polyhedralBoundary` in a different
module. Regenerating `BoundaryInvariance` and `PolyhedralBoundary` from the S
sources with the prescribed checker restored a consistent import environment;
both regeneration checks also exit 0. `AuditS16.lean` checks twelve declarations,
including the new chain and the planar prescribed-triangle endpoint, with only
the three standard foundational axioms and exit 0.

The remaining gap is the free-triangle operation for a disk in the spherical
boundary: transfer the local planar deletion through a vertex-star chart,
prove its effect on the whole disk, and iterate while retaining the prescribed
triangle. Neither the adapted triangulation nor the chart conjugation alone
closes the disk-to-facet theorem 17.5 or its consumers 17.6 and 17.8.

## Native disk recognition and pure-dimensional meshes

Native PL balls and spheres are now proved nonempty, and `LinkDimension`
proves that every face of a finite triangulation of an n-dimensional PL ball
or sphere is contained in a face with n + 1 vertices. The proof inducts on
vertex links; it does not assume purity or a special triangulation. This
supplies `IsPure2` for `planeComplexOfSimplicialComplex` when the native space
is a PL two-ball, so its upstream triangle mesh has exactly the native support.
The existing support proof now uses `Finset.subtype_map_of_mem` for the vertex
lift instead of repeating a manual subtype construction.

The existing interior-image lemma in `FrontierBoundary` is promoted without
changing its statement or proof. `BallFrontier` uses it to prove nonempty
interior and `closure (interior P) = P` for full-dimensional positive-dimensional
PL balls in Euclidean space. `PlanarSchoenflies` then recognizes every given
planar `IsPLBall 2 D` as `J.closedRegion` for some polygonal circle J. The
converse is included, giving an exact equivalence for the native predicate.

`exists_isPLHomeomorphOn_remove_geometricallyFree_triangle` now accepts the
native PL-ball hypothesis on an upstream mesh. It produces a global PL
homeomorphism supported in any prescribed open neighborhood of the free
triangle, gives the image of the whole disk as the erased mesh, and proves
that the erased support remains a native PL ball. The retained-triangle
induction uses this kernel, and new corollaries accept a native PL ball both
for prescribed-mesh-triangle straightening and for unrestricted straightening.
No vendor Lean source is modified; the polygonal recognition and free-triangle
facts are used from the existing vendored closure.

All five affected modules pass focused checks with exit 0 and zero warnings.
`AuditS17.lean` audits twenty-one declarations, including these producers,
the existing S.1 endpoints, 17.4, and the vertex-star extension. Every closure
contains only `propext`, `Classical.choice`, and `Quot.sound`; the audit exits 0.
The planar kernel still has to be transported to a local disk in the
triangulated tetrahedral boundary with control of the rest of that boundary.
The whole spherical-disk image statement and its induction remain open;
17.5, 17.6, and 17.8 are not claimed complete.

## Native integration with planar arc gluing

The S branch incorporates F through `8c1ce1d4f` by an ordinary merge, preserving
published history. Native duplicate declarations are consolidated:
`IsPLBall.isPolyhedron` remains once in `PLImage`; `geometricLink_simplexComplex`
uses the canonical declaration in `SimplexLink` with its face inferred;
`boundaryComplex_simplexComplex` uses the canonical declaration in
`BoundaryOfBall`, carrying the ambient `DecidableEq` instance. The two copies
in `SimplexBoundaryImage` are removed; its boundary-image consumer retains its
statement and passes the focused check. No vendor Lean source is modified.

The synchronization retains S's completed P.1 and P.2 results and records F's
additional native arc matching, crosscut, and disk gluing inputs separately.
All 39 selected changed or affected native modules pass the prescribed focused
checks with exit 0 and zero warnings. `AuditS18.lean` reviews 127 declarations
across the integrated S proof chain and the new F interfaces. Each transitive
closure contains only the three standard foundational axioms; the audit exits 0.

## Euclidean vertex-star coordinates and boundary support

`SimplexAffine` constructs an affine PL homeomorphism between finite simplices
with a prescribed vertex bijection, including simplices in different ambient
spaces. `SimplexBoundaryImage` transports their boundaries through an arbitrary
PL homeomorphism. `SimplexBoundary` identifies the open simplex with the closed
simplex minus its boundary, including empty and zero-dimensional cases.

`SimplexCorner` identifies the boundary as the vertex star union the opposite
facet, and identifies the open star by deleting the facet boundary from the
closed star. `SimplexCornerChart` now produces Euclidean coordinates of the
correct dimension, affine on every original star face. These coordinates send
the star boundary to the actual frontier and the open star onto the actual
interior of a Euclidean simplex; the two-dimensional instance is a planar chart.

The ambient extension in `SimplexCornerExtension` is strengthened to fix the
entire opposite facet pointwise; the existing public endpoint is retained as
a corollary. Chart conjugation in `SimplexCornerChart` permits a different target
ambient space and includes the exact image formula for every subset D of the
simplex boundary: the star part is transformed by the conjugate, and D outside
the star remains pointwise fixed. The inner and outer cones are still produced
from the simplex and the prescribed open neighborhood, not supplied as hypotheses.

These are native constructions using the already documented Moise 17.5 route;
no vendor Lean source is modified. All six changed native modules pass focused
checks with exit 0 and zero warnings. `AuditS19.lean` audits eighteen declarations,
including the new coordinate and extension chain and existing P.1, S.1, and 17.4
consumers; all closures use only the standard three axioms and the audit exits 0.
This settles coordinate and support transport, but not the local deletion theorem
for the spherical mesh or its retained-triangle induction. The full 17.5, 17.6,
and 17.8 endpoints remain open.

## Disks inside simplex vertex stars

`PLImage` now constructs the image complex of a map affine on every face
without further subdivision, with an exact correspondence of faces. The
existing general image theorem uses this construction after choosing its
affine subdivision. `simplicialMap_eq_of_forall_affineOn` is moved unchanged
from `Subcomplex` to its prerequisite `PLImage`, preserving its public name
and avoiding a duplicate proof. Both existing image consumers are checked.

`SimplexCorner` proves that a straight simplex contained in an original
vertex open star lies in one original star face. This follows from its
centroid and barycentric support, and requires neither affine independence
of the smaller simplex nor finite-dimensionality of the ambient space.
Consequently the existing star coordinates are affine on every face of
any finite triangulation whose whole space lies in that open star.

`PlanarSchoenflies` bridges the prescribed-triangle result to an arbitrary
native finite triangulation of a planar PL two-ball. `SimplexDisk` transports
this construction through the Euclidean vertex-star coordinates and the
supported ambient extension. It straightens a disk lying in one vertex
open star to any specified triangle of its triangulation, preserves the
whole simplex, and fixes both the opposite facet and the complement of the
prescribed open neighborhood. A second endpoint produces such a triangle
from an arbitrary native PL disk. No geometric extension is assumed.

No vendor Lean source is modified. All five changed native modules and the
`IsomorphicSubdivision` and `GeneralPosition` consumers pass the prescribed
focused checks with exit 0 and zero warnings. The shared boundary artifacts
again required regeneration from the S sources; both regeneration checks
exit 0. `AuditS20.lean` audits fourteen declarations with only `propext`,
`Classical.choice`, and `Quot.sound`, and exits 0.

The hypothesis that the whole disk lies in one original open star is
substantive. A general disk on the tetrahedral boundary can meet several
stars, and its intersection with a star need not be a disk. The relative
local deletion operation and the global retained-triangle induction remain
open; this result does not close Moise 17.5, 17.6, or 17.8.

## Closed-star control under further subdivision

`StarSubdivision` proves that the closed star of a point in a face lies
in the union of the closed stars of that face's vertices. Combined with
the existing subdivision containment from `LinkRadial`, this shows that
any further subdivision preserves a cover controlling those unions of
closed stars. No finiteness, open-cover, or finite-dimensional hypothesis
is needed for the inheritance theorem. In particular, affine common
refinements preserve the open-star control already produced for the
spherical disk mesh. No vendor Lean source is modified.

The focused module check exits 0 with zero warnings. `AuditS21.lean`
audits the three new declarations, the adapted-mesh producer, and both
vertex-star disk-straightening endpoints; all six closures contain only
the standard three axioms and the audit exits 0. This settles refinement
stability, not the relative spherical free-triangle deletion operation.

## Final integration with crosscut triangulations

The final synchronization incorporates F through `d0902b2cd` by an ordinary
merge on the S branch. It adds the native crosscut restriction and boundary
formulas, strict triangle-count decrease, incident triangle existence, and
supporting results in `Combinatorial`, `Subcomplex`, `BoundaryInvariance`,
and `PlanarJordan/Regions`. The new copy of `IsPLSphere.nonempty` in F's
`PLBallSphere` is removed in favor of the earlier canonical declaration in
`Polyhedron`; the public name and statement are unchanged. No vendor Lean
source is modified. S's completed P.1 and P.2 endpoints remain recorded as
complete; the independent F proof route is documented separately.

Twelve changed or affected native modules pass the final focused checks
with exit 0 and zero warnings. `AuditS22.lean` audits 198 distinct declarations
in the integrated environment, including explicit three-dimensional frontier
and planar boundary-extension specializations, the planar and local spherical
disk chain, and the native F crosscut inputs. Every transitive closure contains
only `propext`, `Classical.choice`, and `Quot.sound`; the audit exits 0.
Final logs are `.lake/scratch/final3-*.log` and
`.lake/scratch/audit-final3-s.log`. The plans retain the full 17.5, 17.6,
and 17.8 goals as open, and describe the local-deletion gap explicitly.

## Relative planar deletion and native erased complexes

The S checkpoint merges `origin/codex/moise-integration` through `74117a65b`
without conflicts in merge `bbf60272f`. Four incoming covering and Euler
modules pass the prescribed focused checks with exit 0 and zero warnings.
`AuditS26.lean` checks 31 distinct integrated endpoints with only the standard
three axioms. No vendor Lean source is modified by the merge.

`PlanarSchoenflies` strengthens both free-triangle deletion cases and their
combined endpoint to record that the original frontier outside the removed
triangle is fixed pointwise. The original public signatures remain as
corollaries. These properties follow from the existing thin-kite construction
and its inverse; they are not new hypotheses.

`PlanarFreeFace` identifies the support of the upstream erased triangle mesh
with native `eraseTriangleComplex`. It chooses a triangle distinct from a
prescribed retained triangle, a face-star center of cardinality one or two,
and proves that deletion leaves a PL disk. For every open neighborhood of
the chosen triangle it also produces a global PL homeomorphism with the
exact erased-disk image, fixed outside that neighborhood and on the rest
of the original frontier. The older face-star-center statement is preserved
as a corollary. Three redundant native tactics are removed for zero warnings.

Both changed native modules pass the prescribed focused checks with exit 0
and zero warnings. `AuditS27.lean` checks 11 distinct declarations with only
`propext`, `Classical.choice`, and `Quot.sound`, and exits 0. Logs are
`.lake/scratch/check-planar-relative-deletion.log`,
`.lake/scratch/check-native-planar-deletion.log`, and
`.lake/scratch/audit-planar-relative-deletion.log`.

This closes the native planar deletion bridge. The local spherical deletion
and the retained-triangle induction needed for full Moise 17.5 are still
open; 17.6 and 17.8 are not claimed complete.

## Deletion from the face star of a free triangle

`PlanarFreeFace` now derives the upstream geometric free-triangle condition
from the native frontier trace: one or two facets opposite the vertices of
a face-star center. The triangle count argument is factored out and reused.
`FaceStarBoundary` proves that the open simplex of the center lies in the
interior of the disk. Three unused assumptions are removed from its earlier
support and trace lemmas, and every in-tree consumer is updated.

The new native `FaceStarDeletion` module applies the deletion to the face
star itself. It proves the face star is a PL disk, that the triangle has
the same frontier trace there, and that the star has more than one triangle.
The last point follows from the center being interior to the star but on
the triangle frontier. Thus no unproved local-disk or nondegeneracy input
is added. The result is a global planar PL homeomorphism with exact local
erased-disk image, fixed outside the prescribed neighborhood and on the
rest of the star frontier. No vendor Lean source is modified.

All three changed native modules pass focused checks with exit 0 and zero
warnings. `AuditS28.lean` checks nine distinct declarations with only the
standard three axioms and exits 0. Logs are
`.lake/scratch/check-planar-frontier-trace.log`,
`.lake/scratch/check-face-star-boundary.log`,
`.lake/scratch/check-face-star-deletion.log`, and
`.lake/scratch/audit-face-star-deletion.log`.

Transport to spherical charts, compatibility with the rest of the original
disk, and the final retained-triangle induction remain required for 17.5.
The statements of 17.5, 17.6, and 17.8 are unchanged and remain open.

## Protected edge families in relative triangle deletion

The resumed S branch starts from `5d7a83446`, including the interleaved
face-star work in `e21341229` and the unverified relative thin-kite handoff.
The native `RelativeThinKite` development adapts the finite edge-avoidance
and thickness arguments from upstream `Moise/FreeTriangleMove.lean` and
`Moise/PolygonalSchoenflies.lean`, using `Moise/ThinKiteMove.lean` for the
geometric segment estimate. The upstream files and their Apache-2.0
attribution remain preserved in this vendor tree; no vendor Lean source
is modified.

The new relative lemmas choose a single sufficiently small positive
thickness for a finite family, fix its union pointwise, retain the old
frontier control, and stay in the requested open neighborhood.
`PlanarSchoenflies` threads that family through both deletion cases and
the combined endpoint, retaining the previous signatures as corollaries.
The remaining source error in the handoff is repaired by converting
triangle membership through `TriangleMesh.toPlaneComplex_cells` before
using `PlaneComplex.mem_simplexes_of_mem_cells`.

After reading the current branch sources, `RelativeThinKite`,
`PlanarSchoenflies`, `FaceStarBoundary`, `PlanarFreeFace`, and
`FaceStarDeletion` are rebuilt in dependency order with the prescribed
checker. Every final check exits 0 with zero warnings. `AuditS29.lean`
checks 23 distinct declarations, including every public declaration in
the three face-star modules and the new protected-family endpoints.
All closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
The audit exits 0; logs are `.lake/scratch/resume-*.log` and
`.lake/scratch/audit-resume-s29.log`.

The protected-family condition is still an explicit geometric input at
this layer. Its production for retained spherical triangles and the full
17.5 induction remain open; 17.6 and 17.8 remain unchanged.
