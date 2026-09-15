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
region. Its public statement does not certify PL behavior on the whole plane; the
native consumer bridge and that stronger relative endpoint remain separate work.
