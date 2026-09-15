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

## Local deletion inside a planar ambient mesh

The native `PlanarRelativeDeletion.lean` module combines the previously
verified protected-family moves with upstream
`PolygonalCircle.eq_closedRegion_of_isCompact_frontier_eq` and
`TriangleMesh.exists_edge_of_mem_frontier_triangle`. A planar PL disk is
preserved by any ambient homeomorphism preserving its frontier. Fixing
the finite edge family therefore preserves every protected triangle as
a set. Splitting a mesh into a restricted disk and the retained triangles
then gives the exact image of the entire mesh after one deletion.

The ambient mesh is not assumed to be a disk. The local disk, free-edge
trace, and explicit intersection conditions for the retained triangles
are the inputs at this interface. Producing these conditions in the
spherical charts and the retained-triangle induction are still needed
for 17.5; 17.6 and 17.8 remain open. This is native assembly of the
vendor's planar results, with no vendor Lean source changes.

The focused check exits 0 with zero warnings. `AuditS30.lean` checks all
four new public declarations with only `propext`, `Classical.choice`,
and `Quot.sound`, and exits 0. Logs are
`.lake/scratch/check-planar-relative-deletion.log` and
`.lake/scratch/audit-planar-relative-deletion.log`.

## Free-triangle intersection conditions and simplicial transport

`PlanarRelativeDeletion` now derives the protected-intersection conditions
for both free-triangle cases. The one-edge proof uses upstream
`isBoundaryEdge_freeTriangleBaseEdge_of_oneEdgeFree` and incidence-one
uniqueness. The two-edge proof uses
`exists_polygonalDisk_eraseTriangle_of_twoEdgeFree`, including its exact
intersection of the remaining disk with the deleted triangle, and
`vertex_mem_edge_of_position_mem_edgeCarrier`. No local claim that a
chart intersection is a disk is introduced.

The native `PlanarFreeFace` primary theorem
`exists_isPLBall_eraseTriangleComplex_with_intersections` chooses a free
triangle different from the retained triangle and supplies intersection
bounds for every maximal triangle outside the chosen face star. The old
public signature is retained as a corollary. The native
`FaceStarTransport` module proves that simplicial isomorphisms preserve
face inclusion, intersections, intersection cardinalities, and face
stars. No vendor Lean source changes are made.

`PlanarRelativeDeletion`, `PlanarFreeFace`, `FaceStarTransport`, and the
`FaceStarDeletion` consumer pass focused checks with exit 0 and zero
warnings. `AuditS32.lean` checks 15 distinct declarations, including all
new endpoints and the existing deletion consumers, and exits 0. Every
closure contains only the standard three axioms. Logs are
`.lake/scratch/check-planar-free-face-intersections.log`,
`.lake/scratch/check-face-star-transport.log`,
`.lake/scratch/check-face-star-deletion-intersections.log`, and
`.lake/scratch/audit-planar-free-face-transport.log`.

The remaining 17.5 work is to assemble these data on the fixed spherical
triangulation, preserve the whole disk under each chart extension, and
perform the retained-triangle induction and final move to an original
facet. The full 17.5, 17.6, and 17.8 endpoints remain open.

## Intrinsic boundary traces and free faces beyond the plane

The native `FaceStarTransport` API now includes erasure and convex-hull
images. Its intersection proof uses Mathlib's
`Finset.image_inter_of_injOn`. `BoundaryTraceTransport` combines these
with native boundary invariance to transport the exact intersection of
an intrinsic manifold boundary with a simplex.

`FreeFaceTransport.exists_isPLBall_eraseTriangleComplex_of_isGlueIso_planar`
transfers the planar free-face producer to any finite-dimensional ambient
space with a finite disk mesh simplicially isomorphic to a planar disk.
It retains the specified triangle, transports the intrinsic boundary
trace and all protected intersection bounds, and proves the erased mesh
is a PL disk. All these conclusions are produced from the planar result;
none is added as an input. Vendor Lean sources remain unchanged.

The three modules pass focused checks with exit 0 and zero warnings.
`AuditS33.lean` checks nine distinct public declarations, exits 0, and
contains only the standard three axioms. Logs are
`.lake/scratch/check-boundary-trace-transport.log`,
`.lake/scratch/check-free-face-transport.log`, and
`.lake/scratch/audit-boundary-free-face-transport.log`. The full ambient
extension and finite deletion induction for 17.5 remain to be assembled.

## A fixed compatible planar model for an embedded disk

The native `PlanarDiskSubdivision` module starts with a PL disk inside a
finite ambient complex. It produces a finite ambient subdivision, keeps
the disk as a subcomplex, constructs a simplicial isomorphism from that
subcomplex to a planar PL disk, and retains the closed-star containment
in original vertex stars. Relative derived subdivision extends the disk
subdivision to the ambient complex. Thus no further refinement is needed
to obtain the planar model during the deletion induction. The reference
plane triangle uses the vendored standard triangle and its affine
independence; all subdivision and extension steps are native.

The focused check exits 0 with zero warnings. `AuditS34.lean` checks
`exists_isSubdivision_subcomplex_isGlueIso_planar`, exits 0, and reports
only the standard three axioms. Logs are
`.lake/scratch/check-planar-disk-subdivision.log` and
`.lake/scratch/audit-planar-disk-subdivision.log`. This is initial data
for 17.5, not the ambient deletion induction itself.

## Relative deletion for native planar subcomplexes

The native `PlanarSubcomplex` module realizes a pure two-dimensional
subcomplex with the parent complex's vertex type and ordering. Its support,
restriction, and triangle-erasure identities retain those shared vertices.
`PlanarRelativeSubcomplex` applies the previously adapted protected-family
thin-kite construction to a PL subdisk of an arbitrary pure planar complex.
It proves the exact image of both the whole complex and the local disk
after erasing the chosen free triangle. The whole complex is not assumed
to be a disk. Its outside triangles satisfy explicit incidence conditions,
as supplied by the native free-face producer. No vendor Lean file changes.

Both new modules pass focused checks with exit 0 and zero warnings.
`AuditS35.lean` checks all seven public declarations and reports only
standard foundational axioms. Logs are
`.lake/scratch/check-planar-subcomplex.log`,
`.lake/scratch/check-planar-relative-subcomplex.log`, and
`.lake/scratch/audit-planar-relative-subcomplex.log`. The full 17.5 ambient
extension and finite induction, and the 17.6/17.8 consumers, remain open.

## Local boundary data and deletion in a planar chart

`FaceStarTrace` transports a disk's free-triangle boundary trace through
its planar simplicial model. It proves the corresponding intrinsic
boundary trace for the chosen face star and proves that this face star
is larger than the triangle. `AffineImageTransport` exposes the
simplicial isomorphism induced by a map that is affine on every face and
injective on the support, without subdividing the source mesh.

`PlanarChartDeletion` combines these transport APIs with relative
subcomplex deletion. It gives a globally PL plane homeomorphism with
prescribed support and the exact erased image of the entire chart
complex. The chart complex need not itself be a disk. These are native
adaptations of the existing free-face construction; vendor sources are
unchanged.

All three modules pass focused checks with exit 0 and zero warnings.
`AuditS36.lean` checks the three new endpoints, exits 0, and reports only
the standard three axioms. Logs are `.lake/scratch/check-face-star-trace.log`,
`.lake/scratch/check-affine-image-transport.log`,
`.lake/scratch/check-planar-chart-deletion.log`, and
`.lake/scratch/audit-planar-chart-deletion.log`. The ambient assembly and
retained-triangle induction for 17.5 are still pending.

## Ambient deletion on a tetrahedral boundary

The native `GeneratedSubcomplex` and `TriangleSubcomplex` APIs isolate the
triangles contained in a chart and express the entire support, before
and after deletion, as a union with the fixed part in the opposite face.
The face star and its intrinsic boundary data survive this restriction.

`SimplexDiskDeletion.exists_isPLHomeomorphOn_eraseTriangleComplex_on_simplexBoundary`
now assembles one ambient deletion. It uses the native tetrahedral vertex
chart, the adapted planar protected-family deletion, and the previously
checked cone extension. The ambient PL homeomorphism preserves the solid
tetrahedron, maps the whole disk to its erased complex, and fixes the
complement of the prescribed neighborhood. No disk assumption is made on
the intersection with the vertex chart. Vendor Lean sources are unchanged.

All three modules pass focused checks with exit 0 and zero warnings.
`AuditS37.lean` checks all 16 new public declarations, exits 0, and reports
only standard foundational axioms. Logs are
`.lake/scratch/check-generated-subcomplex.log`,
`.lake/scratch/check-triangle-subcomplex.log`,
`.lake/scratch/check-simplex-disk-deletion.log`, and
`.lake/scratch/audit-simplex-disk-deletion.log`. The full 17.5 endpoint
still requires the finite retained-triangle induction and the final
comparison with an original facet; 17.6 and 17.8 remain open.

## Full ambient disk straightening on a tetrahedron

`SimplexDiskStraightening` closes Moise 17.5. The free-face producer avoids
one specified mesh triangle. Recursion on the finite number of triangles
composes the ambient deletions on a fixed compatible subdivision and a
fixed planar simplicial model. The recursion terminates by the strict
triangle-count decrease. Finally, the original disk and an original
facet are each sent to the same retained mesh triangle, and one map is
composed with the inverse of the other.

The public endpoint
`exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron` starts only with
four affinely independent points in Euclidean three-space, an arbitrary
PL two-ball in their convex hull's frontier, and an open neighborhood of
the solid tetrahedron. It produces a global PL homeomorphism preserving
the tetrahedron, sending the disk to an original facet, and fixing the
neighborhood's complement. No mesh, planar model, or conditional
Brouwer class remains in this endpoint. Vendor Lean sources are unchanged.

The focused check exits 0 with zero warnings. `AuditS38.lean` checks all
four new endpoints and the full public signature, exits 0, and reports
only the standard three axioms. Logs are
`.lake/scratch/check-simplex-disk-straightening.log` and
`.lake/scratch/audit-simplex-disk-straightening.log`. The 17.6 and 17.8
consumers are the next layer.

## Tetrahedral push property and simply embedded spheres

The native `TetrahedronPush.hasPushProperty_convexHull_simplex` closes
Moise 17.6 by straightening an arbitrary boundary disk with 17.5,
applying the established simplex-face push theorem 17.4, and transporting
back using the established ambient invariance 17.7. The original push
neighborhood condition `C \ J ⊆ interior N` is unchanged.

`SimplyEmbedded.IsSimplyEmbedded` retains the PL sphere condition and
the requirement for every convex open neighborhood, with an ambient
PL straightening fixed outside that neighborhood.
`exists_hasPushProperty_of_isSimplyEmbedded` closes 17.8: it produces a
bounded PL three-ball with the given frontier and the push property.
Neither endpoint contains an unproved producer assumption. Vendor Lean
sources are unchanged.

Both modules pass focused checks with exit 0 and zero warnings.
`AuditS39.lean` checks all ten public definitions and endpoints in the
17.4-17.8 suite, including the final 17.5, 17.6, and 17.8 signatures and
the full single-embedding definition. It exits 0; all axiom closures are
exactly `propext`, `Classical.choice`, and `Quot.sound`. Logs are
`.lake/scratch/check-tetrahedron-push.log`,
`.lake/scratch/check-simply-embedded.log`, and
`.lake/scratch/audit-s2-push-property.log`. S.2 is complete. The 17.9-17.12
developments and the general cell-decomposition versions of P.3 remain
separate pending work.

## Relative polyhedral neighborhoods for three-dimensional push moves

The native `PolyhedralSeparation.lean` adds finite piecewise affine
nonnegative defining functions for polyhedra, polyhedral sublevels, and
`exists_isPolyhedron_neighborhood_sdiff`. For polyhedra C and A and an
open set U containing C, this constructs a polyhedron N with
`C \ A ⊆ interior N`, `N ⊆ U`, and `N ∩ A = C ∩ A`.
This supplies the controlled closed neighborhoods used in Moise 17.9
and 17.11 (printed pages 121-122). The construction is native and uses
finite maxima and minima of affine functions; no vendor source changes
were made. It is a neighborhood input, not completion of those theorems.

The focused check exits 0 with zero warnings. `AuditS40.lean` checks all
four new declarations, exits 0, and reports only `propext`,
`Classical.choice`, and `Quot.sound`. Logs are
`.lake/scratch/check-polyhedral-separation.log` and
`.lake/scratch/audit-polyhedral-separation.log`.

## Protected push moves and complementary disks on PL two-spheres

Four native modules add inputs to the Moise 17.9-17.11 arguments.
`RelativePush.lean` uses the relative polyhedral neighborhood to realize
a push while fixing a protected polyhedron, under the explicit
intersection and density conditions used by the book. It also gives the
exact image of the union of the moving disk and protected set.
`PLHomeomorphTopology.lean` transports closures of subsets of compact
PL homeomorphism domains. `SimplexFacetComplement.lean` identifies the
closure of a simplex boundary minus one facet and its intersection with
that facet. `SphericalDiskComplement.lean` uses the verified 17.5 to
identify an arbitrary PL two-sphere with a tetrahedral boundary while
sending a prescribed disk to a facet. It proves that the complementary
closure is a PL two-ball and that the two disks intersect in exactly
the intrinsic boundary from any disk parametrization.

These are native arguments and consequences of earlier native results;
no vendor Lean source was changed. They do not yet prove 17.9, 17.10,
or 17.11, and do not assert the general cell-decomposition version of P.3.
Each of the four focused module checks exits 0 with zero warnings.
`AuditS41.lean` checks all seven new declarations, exits 0, and reports
only `propext`, `Classical.choice`, and `Quot.sound`. Logs are
`.lake/scratch/check-relative-push.log`,
`.lake/scratch/check-pl-homeomorph-topology.log`,
`.lake/scratch/check-simplex-facet-complement.log`,
`.lake/scratch/check-spherical-disk-complement.log`, and
`.lake/scratch/audit-spherical-disk-complement.log`.

## Convex open neighborhoods of compact frontiers

The native `Analysis/Convex/CompactFrontier.lean` proves that an open
convex set containing the frontier of a compact set contains the whole
compact set, in any nontrivial real normed space. This justifies the
support containment used in Moise 17.9 and 17.11. It uses Hahn-Banach
separation and an extremum argument, with no finite-dimensional
assumption and no vendor source edits. The focused check exits 0 with
zero warnings; `AuditS42.lean` exits 0 and reports only the three standard
axioms. Logs: `.lake/scratch/check-compact-frontier.log` and
`.lake/scratch/audit-compact-frontier.log`.

## Cones from interior points of convex polyhedra

The native `ConvexCone.lean` proves that a simplicial complex contained
in the frontier of a closed convex set is a cone base for any interior
point. Supporting affine functions at face centroids vanish on the
whole face. It also identifies the cone over the full frontier with
the original compact convex set. The supporting ray lemma in
`Analysis/Convex/CompactFrontier.lean` holds for arbitrary compact sets
and uses a maximum on a line, without a finite-dimensional assumption.
These are inputs to Moise 17.9 (printed page 121), not yet its ambient
PL straightening conclusion. Vendor Lean sources are unchanged.

Both focused checks exit 0 with zero warnings. `AuditS43.lean` checks
all three new declarations, exits 0, and reports only `propext`,
`Classical.choice`, and `Quot.sound`. Logs:
`.lake/scratch/check-compact-frontier.log`,
`.lake/scratch/check-convex-cone.log`, and
`.lake/scratch/audit-convex-cone.log`.

## Boundaries of cones over PL balls

The native `ConeBoundary.lean` identifies the frontier of a cone over
an (n+1)-dimensional PL ball in an (n+2)-dimensional real normed space
as the union of the base and the cone over its intrinsic boundary.
It transports the cone to a simplex, computes its facets, and uses
boundary invariance. The companion `PLHomeomorphTopology.lean` results
transport interiors and closed-domain frontiers between equal-dimensional
real normed spaces. `InvarianceOfDomainManifold.lean` adds the required
normed-space form of invariance of domain by continuous linear transport
to Euclidean space. Existing signatures are unchanged.

These native inputs support the deletion argument of Moise 17.10
(printed page 121). No vendor Lean sources were modified, and the
ambient straightening conclusion of 17.10 remains pending.
The three changed modules and the complementary-disk consumer pass
focused checks with exit 0 and zero warnings. `AuditS44.lean` checks
five declarations (including the prior closure transport), and
`AuditS45.lean` checks the two cone-boundary declarations. Both exit 0;
all seven axiom closures contain only the standard three axioms.
Logs: `.lake/scratch/check-invariance-domain-normed.log`,
`.lake/scratch/check-pl-homeomorph-topology.log`,
`.lake/scratch/check-cone-boundary.log`,
`.lake/scratch/check-spherical-disk-complement.log`,
`.lake/scratch/audit-pl-homeomorph-topology.log`, and
`.lake/scratch/audit-cone-boundary.log`.

## Deleting a free tetrahedron from a triangulated PL three-ball

Four native modules supply the single deletion step used by Moise
17.9-17.10 (printed page 121). `BoundaryFacets.lean` characterizes a
boundary facet by its unique coface and generates a PL ball boundary
from its facets. `SubcomplexComplement.lean` computes closures of
subcomplex differences. `BoundaryDeletion.lean` proves the exact
change of the intrinsic boundary after deleting one top-dimensional
simplex, in every dimension, when the remaining complex is a PL ball.

`TetrahedronDeletion.lean` realizes the corresponding frontier change
by an ambient PL homeomorphism fixed outside any prescribed open
neighborhood of the deleted tetrahedron. Its free-face hypothesis is
that the intersection of that tetrahedron with the original frontier
is a PL two-ball. The proof derives the protected complementary disk
and its density condition, then applies the verified tetrahedral push
property. This closes a deletion step, not the full finite induction
for 17.9 or 17.10. Vendor Lean sources remain unchanged.

All four focused checks exit 0 with zero warnings. `AuditS46.lean`
checks all seven declarations, exits 0, and reports only `propext`,
`Classical.choice`, and `Quot.sound`. Logs:
`.lake/scratch/check-boundary-facets.log`,
`.lake/scratch/check-subcomplex-complement.log`,
`.lake/scratch/check-boundary-deletion.log`,
`.lake/scratch/check-tetrahedron-deletion.log`, and
`.lake/scratch/audit-tetrahedron-deletion.log`.

## Supported ambient straightening of cones over PL two-balls (Moise 17.10)

The native `ConeStraightening.isSimplyEmbedded_frontier_coneComplex`
proves Moise 17.10 (printed page 121) for any finite simplicial complex
whose space is a PL two-ball and any `IsConeBase` apex. The conclusion
is the full `IsSimplyEmbedded` predicate, including an ambient PL
homeomorphism fixed outside every prescribed convex open neighborhood
of the boundary. It has no unproved topological producer assumption.

`ConeFreeFace.lean` computes the boundary trace of a cone simplex and
proves that coning a free base face produces the required PL disk.
`ConeDeletion.lean` combines the face-deletion relation with the
previous ambient tetrahedron deletion. `ConeStraightening.lean` keeps
one base triangle and recurses on the strictly decreasing number of
triangles, using the same open neighborhood throughout. A general PL
two-ball is first subdivided into a complex with a planar simplicial
isomorphism; `PlanarDiskSubdivision.lean` adds that direct interface.
`Cone.lean` adds uniqueness of positive radial representations.
Vendor Lean sources are unchanged. The proof follows the book's
finite deletion argument and supplies the explicit boundary and
support bookkeeping. The 17.9 and 17.11 endpoints and the general
cell-decomposition version of 17.2 remain pending.

All five changed modules pass focused checks with exit 0 and zero
warnings. `AuditS47.lean` checks all eight new declarations and the
full 17.10 signature, exits 0, and reports only `propext`,
`Classical.choice`, and `Quot.sound`. Logs:
`.lake/scratch/check-cone.log`, `.lake/scratch/check-cone-free-face.log`,
`.lake/scratch/check-cone-deletion.log`,
`.lake/scratch/check-planar-disk-subdivision.log`,
`.lake/scratch/check-cone-straightening.log`, and
`.lake/scratch/audit-cone-straightening.log`.

## Supported ambient straightening of convex PL three-balls (Moise 17.9)

The native `ConvexStraightening.lean` proves
`isSimplyEmbedded_frontier_of_convex` from convexity and PL three-ball
structure. Polyhedrality follows from the latter and is not a separate
hypothesis. The conclusion retains the ambient PL homeomorphism fixed
outside every prescribed convex open neighborhood of the frontier.

Following printed page 121, the proof cones a boundary triangulation
from an interior point and deletes one tetrahedron. The remaining
base is a PL disk, so the verified 17.10 straightening applies.
`SphericalTriangleDeletion.lean` identifies the remaining complex
with the closure of the complement of a triangle and proves its disk
structure. `ConeIntersection.lean` adds the exact intersection of the
base with a cone simplex. Only frontier images are needed for the
stated endpoint; no unproved claim about images of filled regions is
used. Vendor Lean sources remain unchanged. The 17.11 and general
cell-decomposition 17.2 endpoints are still pending.

All three changed modules pass focused checks with exit 0 and zero
warnings. `AuditS48.lean` checks all four new declarations and the
full 17.9 signature, exits 0, and reports only `propext`,
`Classical.choice`, and `Quot.sound`. Logs:
`.lake/scratch/check-spherical-triangle-deletion.log`,
`.lake/scratch/check-cone-intersection.log`,
`.lake/scratch/check-convex-straightening.log`, and
`.lake/scratch/audit-convex-straightening.log`.

## Complementary disk topology and supported gluing (Moise 17.11 inputs)

`BallInterior.lean` proves that the image of the standard open simplex
is the intrinsic interior of a PL ball, with connectedness and dense
closure. `SphericalDiskComplement.lean` adds the complementary-disk
involution, both boundary-circle identifications, and connectedness
of a sphere with a disk removed. `CompactFrontier.lean` adds the
compact-region containment principle for closed convex targets and
for targets made convex by a homeomorphism.

`DiskGluing.lean` implements both cases on printed pages 121-122. It
pushes one complementary disk while fixing the other, and straightens
the resulting sphere with support in any convex open neighborhood
containing the original two spheres. This intermediate statement
does not yet replace that neighborhood condition by containment of
only the glued sphere; the planar-disk containment argument is still
required for the full 17.11 endpoint. No vendor Lean source changed.

All four changed modules pass focused checks with exit 0 and zero
warnings. `AuditS49.lean` checks all eleven new declarations and the
straightening signature, exits 0, and reports only `propext`,
`Classical.choice`, and `Quot.sound`. Logs:
`.lake/scratch/check-ball-interior.log`,
`.lake/scratch/check-spherical-disk-complement.log`,
`.lake/scratch/check-compact-frontier.log`,
`.lake/scratch/check-disk-gluing.log`, and
`.lake/scratch/audit-disk-gluing.log`.
