# Local modifications

Upstream: https://github.com/mccorvie/classification-of-surfaces, revision e3c7230fe78d7b056a415d9ecae6f77887046b32. The original Apache license, README, source copyright/authors and retained declaration documentation are preserved. UPSTREAM.patch records every source-line change against the pinned originals.

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
