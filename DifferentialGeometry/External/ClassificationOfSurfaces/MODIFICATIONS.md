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

## Native polygon after one-edge deletion

PrePolygonDeletion combines the checked native complementary-arc, Jordan-frontier,
polygonal-frontier and compact-region recognition proofs in one coherent leaf.
Nine declaration statements and proof bodies are preserved; the unused private
edge specialization is omitted. Only
Schoenflies.PrePolygon.exists_prePolygon_closed_region_erase_triangle_of_one_edge_free
is public. Namespace and open scopes remain unchanged. The final engine assumes
only the original mesh frontier equation and actual geometric one-edge freeness;
no original support, remaining-disk or surviving-triangle assumption is added.
It returns an actual remaining PrePolygon with support/frontier, oriented arcs,
endpoint coordinates and exact attaching-set equations.

The compact-region recognition proof adapts PolygonalCircle.eq_closedRegion_of_isCompact_frontier_eq
from PolygonalSchoenflies.lean:2410 at the pinned revision to native IsSeparating
and inside/outside. Its original documentation and Apache notice are preserved.
DELETION_RECOGNITION.patch records the exact zero-context selected-declaration
delta; DELETION_PROVENANCE.json records immutable upstream hashes, the four
checked native source hashes and final module hash. Other new private proofs
use the already integrated native Jordan/polygonal APIs and checked mesh
attachment equations. Consolidation changes only imports, legal notice paths,
the final theorem's visibility and restored upstream recognition documentation,
plus removal of that unused private specialization.

The combined private source passed 1789232885714420646-schoenflies-24adbd8c
with stock declaration linters and standard-only axiom readbacks. The new
production module freshly compiled and its imported public consumer gate passed
1789233891983857661-schoenflies-42a7b73c. Root matched all92 source guards, read
all three type/axiom pairs and verified the exact upstream recognition delta. Geometric free-triangle existence,
the two-edge branch, compatible rounding and smooth disk filling remain open.

## Geometric free-triangle classification

Moise/GeometricFreeTriangle retains seven declarations and their attached
upstream documentation/scopes from FreeTriangleMove. GEOMETRIC_FREE_SELECTION.json
records exact original body hashes and source locations. The import uses the
previously selected OneEdgeAttachment layer; only the modification-notice path
changes locally. The one- and two-boundary-edge cases produce the actual
geometric frontier configurations. The contrary case identifies an actual
isolated boundary vertex and cutting diagonals. It does not assert geometric
freeness exists for every polygonal mesh.

The unchanged bodies and a concrete midpoint two-triangle mesh consumer pass
1789233897698956242-schoenflies-ff473eb1, with stock declaration linters and
standard-only axioms. Final production gate
1789234647397384846-schoenflies-3ad41b77 passed in73.49s, freshly compiling
only the new module. Root matched all nine source guards, read all eight
signature/axiom pairs, and independently matched all seven upstream bodies.
All imported vendor and consumer declaration linters and standard-only axioms
pass. This is not a full DifferentialGeometry aggregate build.

## Mesh partition along a native crosscut

TriangleMeshCrosscut adapts the PolygonalCrosscut mesh-side proofs from the same
pinned upstream revision. It uses the existing native IsCrosscut, IsCutPair,
inside and crosscut_theorem APIs. The chord remains tied to an actual mesh edge
by its convex-hull/segment equality. Canonical restrictTriangles gives both
actual submeshes; no additional mesh alias is introduced. Four proof helpers
remain private, and only restrict_triangles_crosscut_partition is public.
It returns both exact closed-region supports, the finite partition, disjointness,
nonemptiness and both strict triangle-count decreases.

CROSSCUT_PROVENANCE.json records the original locations and hashes.
CROSSCUT_UPSTREAM_SELECTED.lean.txt preserves all ten selected original bodies
and documentation; CROSSCUT_ADAPTATION.patch records their exact adaptation.
Root independently matched those originals against the immutable source and
retained all five checked native proof bodies/scopes. Private source gate
1789235209202169419-schoenflies-6e17e677 passed. Final production gate
1789235455742746297-schoenflies-fb8bd5a2 passed in76.89s, freshly compiling only
the new module. All86 source guards, both public/consumer type-axiom pairs,
all-vendor/current declaration linters and standard-only axioms pass.
The consumer obtains the original mesh from an actual PrePolygon and supplies
an actual boundary-to-boundary mesh edge. Geometric free-triangle existence,
smooth rounding and disk filling remain separate obligations.
