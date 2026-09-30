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

## Mac strict replay from 04ca9612f, 2026-09-23

The published commit retains the pre-replay Lean source although its historical records
describe later Windows repairs. This Mac replay restores required module documentation
in the four adapters below and moves both existing attribution blocks of
`TriangleMeshGeometricFree.lean` verbatim before imports. Non-comment source tokens are
unchanged. The three owner-approved `letI` to `let` replacements in
`Moise/GeometricTriangulation.lean` are also reapplied. No linter is disabled.
These source identities record edits only; accepted compiler receipts are separate.

- `TriangleMeshCrosscut.lean`: SHA-256 `cf4d63e80ec80c8c613708105385bdef7d518d6dd56954138dd90d4e4dd7b003`.
- `PrePolygonDeletion.lean`: SHA-256 `102551c02a10c50b94cbec14a2619547082a9360957d1d054e4650579b9b41c6`.
- `PrePolygonTriangulation.lean`: SHA-256 `ae5963c682c25a014a17a308887a954a7ff7eac6a9dd5e1cf286b2b5de3859c3`.
- `TriangleMeshGeometricFree.lean`: SHA-256 `fd94a84ef8f210d9f266a629c389c36530a4e8abb798c44e3fb04c40da435246`.
- `Moise/GeometricTriangulation.lean`: SHA-256 `fd30a1edc1459f3955174b58f1d10fe1d1e834cfd5034403f59cc686ce478400`.

## Mac strict copyright-header parsing, 2026-09-23

The provenance text following each Authors line is preserved in a separate adjacent
comment so that the standard header linter reads only author names in that field.
Copyright, licensing, attribution and provenance wording are unchanged. No declarations,
proofs or imports change; no linter is disabled. Affected source files:

- `PrePolygonDeletion.lean`
- `TriangleMeshCrosscut.lean`
- `TriangleMeshGeometricFree.lean`
- `PrePolygonTriangulation.lean`

## Mac strict rebuild continuation, 2026-09-23

Following the owner's continuation instruction after the reported hard stop, applied the
previously proposed ten mechanical `letI` to `let` style repairs. No theorem statement
changed; no linter was disabled and no warning receipt was accepted.

- `External/ClassificationOfSurfaces/Moise/ConeExtension.lean`: 1 substitutions at original lines 1014.
- `External/ClassificationOfSurfaces/Moise/PolygonalJordan.lean`: 1 substitutions at original lines 228.
- `External/ClassificationOfSurfaces/Moise/PolygonalCrosscut.lean`: 7 substitutions at original lines 418, 1170, 1213, 1248, 1346, 1396, 1690.
- `External/ClassificationOfSurfaces/Moise/PolygonalSchoenflies.lean`: 1 substitutions at original lines 787.

## Windows integration linter repair, 2026-09-24

- `Moise/PolygonalCrosscut.lean`: removed the unused `[NeZero n]` hypothesis from the private
  `PolygonalCircle.natCast_eq_natCast_of_lt`; its proof and conclusion are unchanged.
  Original licensing, attribution, comments and namespaces are preserved.

## Relocation into the DifferentialGeometry library, 2026-09-24

The merge of `codex/pc-sorry-free` at 0665ab70b7bd2df6e4a48810cf667df04284ad88, which places
all vendored sources under `DifferentialGeometry/External/` and removes the separate `External`
Lean library, moves this vendor from `External/ClassificationOfSurfaces` to
`DifferentialGeometry/External/ClassificationOfSurfaces`. Every internal and consumer import
prefix `External.ClassificationOfSurfaces` becomes
`DifferentialGeometry.External.ClassificationOfSurfaces`; no other source text changes.
Declaration namespaces, statements, proof bodies, licensing and attribution are unchanged.

The incoming branch still carried the source variant recorded above as revision 54ad4d8
(`Moise/GeometricFreeTriangle`, `Moise/OneEdgeAttachment`, `PORTING.md`, `README.md` and the
three reduced base modules), unchanged since that revision. As recorded in
`INTEGRATION_54AD4D8.json`, its selected exports are supplied by the canonical
`Moise/FreeTriangleMove` and `Moise/PolygonalSchoenflies`, and its porting notes and README are
retained here as `SOURCE_54AD4D8_PORTING.md` and `UPSTREAM_README.md`; the parallel copies are
therefore not installed. Historical records keep the module paths current at their time.


# Invariance of domain restoration

Source: `mccorvie/classification-of-surfaces` at
`e3c7230fe78d7b056a415d9ecae6f77887046b32`,
`ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`.
Apache-2.0; original authors Steven Sivek and Kai Lam.

The full selected original source, including all documentation and nested provenance,
is retained in `upstream/selected-topology_e3c7230.tar.gz` (archive member `ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`).
The active adaptation keeps all 16 original declarations in
`External/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`, with their
existing `DifferentialGeometry.Topology` names. It introduces no new declaration
and has no native-only residue. The native module is removed; consumers import
the external module directly. Native homological no-retraction and unconditional
model-space/manifold endpoint modules remain in their mathematical directories.

Changes from the pinned original: current namespace; explicit `{E : Type*}`;
`_root_.Topology` qualification; `ContinuousOn.domRestrict` and
`continuousOn_iff_continuous_domRestrict`; `Set.mem_ofPred_eq`; current local
instance syntax. All original comments and source notices are restored.
After removing comments and whitespace, the adapted source is identical
to the pre-restoration native module. `migration-ClassificationOfSurfaces/InvarianceOfDomain.patch` records exact
source changes.

Nested source provenance remains Kai Lam's Mathlib PR 36770 at
`230d75acb32d80e7d7c4f4cd028b139f3dc28be7` and Steven Sivek's
`TopologicalManifolds` at `05f80330d5a41b05376ae90eb8aa32c0166721db`.

The source map and archive record provenance; compilation and axiom acceptance are verified separately.


# Brouwer ray construction

Source: `mccorvie/classification-of-surfaces`, commit
`e3c7230fe78d7b056a415d9ecae6f77887046b32`,
`ClassificationOfSurfaces/Moise/Brouwer.lean`.
The exact upstream source, including all original documentation, is preserved in
`upstream/selected-topology_e3c7230.tar.gz` (archive member `ClassificationOfSurfaces/Moise/Brouwer.lean`). The original Apache-2.0
license is preserved as `LICENSE`. The adapted Lean file restores the original
ClassificationOfSurfaces copyright and authors header.

## Changes inherited from the native adaptation

- Renamed the namespace from
  `LeanEval.Topology.ClassificationOfSurfaces.Moise` to
  `DifferentialGeometry.Topology.FixedPoint`. Existing current public names are unchanged.
- Generalized `Plane` to an arbitrary universe-polymorphic real inner-product space
  in the ray scale, quadratic identity, sphere endpoint, boundary identity, and
  continuity proofs. These generalized third-party proofs remain in `External`.
- Generalized the retraction construction from the plane disk to a unit ball.
- Replaced the boundary inclusion proof by `Metric.sphere_subset_closedBall`.

## Declaration-level separation

- Moved `fixedPointRayScale` and its six private supporting lemmas to
  `External/ClassificationOfSurfaces/Moise/Brouwer.lean` with their current proof bodies.
- Extracted the inherited retraction construction from the fixed-point theorem into
  `exists_retraction_closedBall_sphere_of_continuous_of_no_fixedPoint`, in the same
  external module. It needs no finite-dimensionality assumption. The new external
  theorem documentation describes its actual generalized conclusion; original
  planar theorem and module documentation are retained verbatim in the snapshot.
- Removed all native-library imports from this external module; it depends only on
  Mathlib and cannot form a cycle through the native no-retraction theorem.
- Kept the native arbitrary-dimensional Brouwer theorem and instance in
  `Topology/FixedPoint/Brouwer.lean`. Its dimension-zero case and use of the native
  homological no-retraction theorem are the library's additions. The positive-dimensional
  proof now consumes the external retraction theorem.
- Kept `Topology/FixedPoint/NoRetraction.lean` native; its proof was not taken from
  the upstream planar no-retraction module.
- Replaced the native InvarianceOfDomain import by the corresponding external module.

`DECLARATION_MAP_topology.json` records the per-declaration classification and source hashes.
`SOURCE_MAP_topology_e3c7230.json` and `migrate_topology_e3c7230.py` replay the integrated split.
No duplicate implementation or alias was introduced.

## Lean 4.34.1 and Mathlib compatibility, 2026-09-27

The dependency upgrade emitted deprecation and unused-simp-argument diagnostics
for the files listed below. These compatibility edits preserve every original
source header, comment, documentation block, attribution, namespace, and
mathematical statement. They introduce no linter suppression or resource option.

- `Moise/PlaneComplex.lean`, `Moise/PolygonalJordan.lean`,
  `Moise/PolygonalCrosscut.lean`, and `Moise/LineSubdivision.lean`: replace the
  diagnosed `if_pos` and `if_neg` references by their current names
  `ite_eq_left` and `ite_eq_right`.
- `Moise/LineSubdivision.lean`, `Moise/ConeExtension.lean`, and
  `Moise/FinitePLHomeomorph.lean`: replace the diagnosed `dif_pos` and `dif_neg`
  references by `dite_eq_left` and `dite_eq_right`. These are direct replacement
  names for the same conditional equations.
- `Moise/FreeTriangleMove.lean`, `Moise/PolygonalSchoenflies.lean`, and
  `TriangleMeshGeometricFree.lean`: remove only the 19 `eq_comm` simp arguments
  reported unused by the upgraded simplifier. The surrounding proofs and all
  declarations retain their original mathematical content.

- `Moise/GeometricTriangulation.lean`: replace deprecated `stdSimplex` uses by
  its exact coordinate predicate, nonnegative coordinates with finite sum one.
  This preserves the existing set-of-functions realization and face interfaces
  definitionally. Obtain closedness and compactness from the current
  `Convexity.StdSimplex` weight embedding and its range formula; prove the
  point-mass membership from `Pi.single_nonneg` and the finite sum formula.
- `Moise/ElementaryMove.lean`: use the same coordinate predicate for the existing
  weight hypothesis and the same point-mass proof for the diamond fan center.
  The geometric objects and conclusions are unchanged.

All comment blocks, line comments, and pre-import attribution text in the 11
modified Lean files were compared byte-for-byte with their pre-upgrade `HEAD`
source and preserved exactly. No source file was moved, renamed, merged, or split.
Direct checks of `Moise/GeometricTriangulation.lean` and `Moise/ElementaryMove.lean`
with the existing Lake setup files and `lean -E warning` exited successfully with
no diagnostics. These checks produced no build artifacts. Complete dependent
compilation, linter, and axiom acceptance remain coordinated repository gates.
