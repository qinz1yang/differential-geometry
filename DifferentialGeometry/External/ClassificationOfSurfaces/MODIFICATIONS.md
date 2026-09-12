# Local modifications

Upstream: https://github.com/mccorvie/classification-of-surfaces, revision e3c7230fe78d7b056a415d9ecae6f77887046b32. The original Apache license, README, source copyright/authors and retained declaration documentation are preserved. UPSTREAM.patch records full-module source changes against the pinned originals. ONE_EDGE_SELECTION.json records the exact immutable sources, declaration locations and unchanged body hashes for the selected attachment layer.

## Selected scope and imports

Only Moise/PlaneComplex, Moise/LineSubdivision and Moise/FreeTriangle are included. The original declaration namespaces remain unchanged. Internal imports now use DifferentialGeometry.External.ClassificationOfSurfaces. No upstream Lake project or dependency configuration is activated.

PlaneComplex omits its unused final barycentric-realization aspect, from mem_simplexes_of_mem_cells through toGeometricTriangulation, and the resulting unused GeometricTriangulation import. Existing mesh, support, intersection, pure-dimensional, affine transport, subdivision and piecewise-linear APIs are retained. FreeTriangle imports LineSubdivision directly instead of the unused ElementaryMove/AmbientHomeomorph chain.

## Lean 4.33.1 compatibility and generality

PlaneComplex reuses Mathlib AffineIndependent.range/mono for finite subfamilies and two subface intersection arguments. The unused point-distinctness input to endpoint_secondCoords_eq_zero_of_two_axis_points is removed, with its documentation adjusted. Three affine transport proofs use explicit carrier/image equalities before transporting unions or dependent vertex indices.

LineSubdivision removes the unused Function.Injective position input from convexHull_image_inter_of_affine_separation and its eight supplied arguments. Six private reference-mesh intersection helpers retain the actual finite vertex and position types and commute both set and finite-set intersections in reversed cases. The reference mesh constructors reuse those helpers, resolving elaboration timeouts without resource overrides.

Seven reindex-support proofs use typed support equalities. Two triangle-enumeration proofs expose the finite-set image before reducing projections. A private typed case eliminator preserves the original localMeshTriangles branch/choice order; six cardinality, independence, monochromaticity, vertex-origin, support and intersection proofs consume it. Three local reference support equalities and four support branches use explicitly typed equations and their compositions. All remaining public constructor/statement headers are preserved.

FreeTriangle retains all 75 mathematical declarations and proof bodies unchanged from upstream. Only its dependency import and modification notice change.

## Module placement

Relative to the already checked scratch sources, production preparation changes only internal import prefixes and the header's modification-record path. No mathematical body, namespace, variable scope, source option, linter or dependency pin changes in this step.

## Native polygon triangulation and geometric attachment

PrePolygonTriangulation adapts PolygonalPolyhedron.lean at the same upstream
revision to the existing Schoenflies.PrePolygon, inside/outside and separation
APIs. It imports no duplicate PolygonalJordan development. All arrangement,
refinement, finite image conversion, support and boundary construction mechanics
remain private. The public exists_simplicial_complex_inside exposes the native
Mathlib finite pure two-dimensional complex with its exact support equation.
The public exists_triangle_mesh_inside derives an actual TriangleMesh with
support equal to closure (inside P.carrier) and frontier equal to P.carrier
from the same private construction. No triangulation assumption is introduced.

The native adapter repairs finite-face transport using the verified
affineIndependent_finset_coe helper, explicit convex-hull image equations and
mem_iUnion₂. AddTorsorBases supplies the pinned convex interior theorem. The
unused Plane simp argument is removed. Relative to checked private source,
production changes only import/header paths, exposes the existing simplicial
result and adds the eight-line mesh existence corollary. UPSTREAM.patch records
the complete zero-context delta from PolygonalPolyhedron.

Moise/OneEdgeAttachment selects 22 ordered-triangle and edge declarations from
FreeTriangleMove and six incidence/intersection/frontier declarations from
PolygonalSchoenflies. All 28 selected declaration bodies, their documentation,
namespace scopes and original attribution are retained unchanged. Unrelated
declarations and dependencies are omitted; only the already ported FreeTriangle
is imported. ONE_EDGE_SELECTION.json records immutable source hashes, exact
upstream declaration locations and selected body hashes. Relative to checked
scratch, only the import prefix and modification-notice path change.

The two new production leaves passed fresh module/import consumer gate
1789231441425991048-schoenflies-788bbe3d. The earlier three-module gate is
preserved separately; exact final evidence is recorded in PROVENANCE.json. There is no claim of geometric free-triangle selection, remaining
polygonal-disk recognition, compatible rounding, or smooth disk filling.
