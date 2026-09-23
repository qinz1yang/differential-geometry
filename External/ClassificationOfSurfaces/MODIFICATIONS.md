# Local modifications for the native planar adapters

## Integration from source revision 54ad4d8ec0408e71da2247daed5ecee2a574f7ec

The existing canonical vendor remains `External/ClassificationOfSurfaces`, pinned to
mccorvie/classification-of-surfaces revision
e3c7230fe78d7b056a415d9ecae6f77887046b32 under Apache-2.0. Existing source,
`LICENSE`, `UPSTREAM_README.md`, `UPSTREAM_ARCHITECTURE.md`, and every earlier
entry of `VENDOR.md` are retained. The incoming license and upstream README are
byte-identical to those existing copies.

Four incoming files are retained: `PrePolygonTriangulation.lean`,
`PrePolygonDeletion.lean`, `TriangleMeshCrosscut.lean`, and
`TriangleMeshGeometricFree.lean`. These combine adapted selected upstream
arguments and locally authored native `Schoenflies` bridges; they are not
represented as four verbatim upstream modules. All existing source copyright,
author lines, public declaration names, declaration documentation, statements,
and proof bodies are retained. The local namespace layout adjustment is recorded
below. The second Alvaro Begue
copyright and density-proof attribution in `TriangleMeshGeometricFree` are
also retained.

The initial source staging changes import lines only. The prepared variant also
contains the layout adjustments recorded below. The three base imports resolve to the already
installed canonical `Moise/PlaneComplex`, `Moise/LineSubdivision`, and
`Moise/FreeTriangle`. Selected `OneEdgeAttachment` declarations are supplied
by the existing `Moise/FreeTriangleMove` and `Moise/PolygonalSchoenflies`;
selected `GeometricFreeTriangle` declarations are supplied by
`Moise/FreeTriangleMove`. `PrePolygonDeletion` directly imports
`Moise/PolygonalSchoenflies` because its proof uses the actual one-edge support,
intersection, and frontier theorems there. Imports between the four adapters
use their canonical `External.ClassificationOfSurfaces` module names.
No duplicate base modules or selected-declaration modules are installed.

The source port's historical records are preserved verbatim as
`SOURCE_54AD4D8_MODIFICATIONS.md`, `SOURCE_54AD4D8_PORTING.md`, and the accompanying
source JSON/patch/text files. Their old selected-port scope, module paths and
historical validation claims describe that source variant, not a fresh build of
this integrated variant. `PROVENANCE.json` has two older top-level target hashes:
for the actual source blobs, use `DELETION_PROVENANCE.json`'s
`production_source_sha256` and `CROSSCUT_PROVENANCE.json`'s `target_sha256`.
The geometric-free existence file is recorded separately by
`GEOMETRIC_FREE_EXISTENCE.json`.

`INTEGRATION_54AD4D8.json` records exact source Git blob identities, source and
staged SHA-256 digests, global import remapping, per-module override, and retained
metadata identities. `INTEGRATION_54AD4D8_COLLISIONS.json` records public-name
checks and the duplicate selected exports supplied by canonical modules.
The initial staging verified that deleting import lines left byte-identical source
text. The subsequent prepared-variant layout changes are recorded separately.
No compiler, transitive axiom, linter, or aggregate acceptance is asserted by
this provenance-only staging step.

## Prepared-variant line-length normalization

`TriangleMeshCrosscut.lean` wraps the private
`restrict_triangles_crosscut_support` conclusion across an additional line.
`TriangleMeshGeometricFree.lean` wraps the private
`isGeometricallyFreeTriangle_of_crosscut_side` hypothesis and
`exists_geometricallyFreeTriangle_of_crosscut_side_card_one` cardinality
hypothesis. These three edits change whitespace only.

The fully qualified public theorem
`LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.exists_two_geometrically_free_triangles_of_jordan_support`
is placed inside that exact namespace, after closing the preceding `Schoenflies`
namespace. A declaration-scoped `open Schoenflies in` supplies its original
Schoenflies name lookup; the circle carrier binder explicitly retains
`Schoenflies.Plane`. The theorem's full public name, binder list, hypotheses,
conclusion, and proof body are retained. The following `Schoenflies` block is
reopened at its original boundary. No variable block or global open scope changes,
and no linter suppression is introduced.

The two affected manifest entries set `only_import_lines_changed` to false,
record the specific normalization, and carry the current prepared source hash.
Their immutable source Git blob and source SHA-256 values remain unchanged.
These edits require the coordinated private checker; no compilation is claimed
by this formatting pass.

## Isolated cone replay, 2026-09-23: GeometricTriangulation instance syntax

The strict Mathlib style linter requests `let` instead of `letI` in proposition proofs.
Changed only the two local finite/decidable instances in
`nonempty_geometricTriangulation_iff_explicit` and the local connected-space instance in
`GeometricTriangulation.faces_isDualConnected_of_isVertexStarConnected`.
Public statements, mathematical proof steps, imports, author attribution and upstream
documentation are unchanged. No linter was disabled. Reverification is required.
Before SHA-256: b399cadf687e0e1ae120af633fef2a1c53723a6e9164034b9269000676fde29f.
After SHA-256: e5b5b859233e2b0b13060c594aeff4bde559cec0fd05916cb33e94477bd95667.

## Isolated replay, 2026-09-23: required adapter module documentation

Added the required mathematical module docstring after imports in the four
adapter files below. In TriangleMeshGeometricFree, moved both existing copyright
and attribution blocks verbatim before imports. All original attribution,
provenance descriptions, declarations and proof bodies are preserved.
No documentation-presence or style linter was disabled.

- External/ClassificationOfSurfaces/TriangleMeshCrosscut.lean: before ffc240ceaa7282ab0fd64171d8204a222ec64e1eab4b4ac67d7336530521403b; after 62b8e9f3051864c0f95286b36e3e85b1454867a8c49868f6fe2d8b3eaa53455d.

- External/ClassificationOfSurfaces/PrePolygonDeletion.lean: before 0b52f138d0195ff1dab7a757eae4979a3467957321d0573533950d29732195de; after 4ad84e3f49c53fc1a892d23454d1c754620dfc1c74defa7f6dc069a359f32e2b.

- External/ClassificationOfSurfaces/PrePolygonTriangulation.lean: before 17f68b191dea414fdceddc681edc63d1fdb39225f55e56c6c069167453e69ba8; after 92aed2d98627852b89ce273052b819b4a6e42c0aee3b1e07f97ab24c35cf2ea8.

- External/ClassificationOfSurfaces/TriangleMeshGeometricFree.lean: before 693a9d0961a7246d7ffd3c86a50a8d305a4b731ce25191bc345c6b8cb0fa1656; after 892b3cb79c377adb40a275bfd903c3f28355f22d7bf8b456e0644ca45f238d9d.
