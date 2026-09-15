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
