# Finite planar meshes

This is a selected vendored dependency from mccorvie/classification-of-surfaces at e3c7230fe78d7b056a415d9ecae6f77887046b32, under Apache-2.0. README.md is the unchanged upstream README; its classification claims and build instructions describe the upstream project. No root NOTICE, CITATION.cff or formalization metadata file was present in the inspected pinned root tree.

The three included modules provide finite geometric simplicial complexes and pure triangle meshes, line refinement with exact support/intersection equations, incidence geometry and weak free-triangle existence. Their support is the union of actual convex hulls; face intersections and affine independence are genuine structure laws. FreeTriangle deletion returns the actual closure-of-difference support and frontier equations. Weak free triangles do not themselves guarantee a remaining disk or geometric freeness.

The original LeanEval.Topology.ClassificationOfSurfaces.Moise namespace is retained. Import through DifferentialGeometry.External.ClassificationOfSurfaces.Moise.FreeTriangle, or a more precise preceding leaf. The existing project supplies Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. The original pins were Lean 4.32.0 and Mathlib 81a5d257c8e410db227a6665ed08f64fea08e997; neither is activated here.

The three exact scratch bodies passed strict Kimina checks with source linters, stock unusedArguments/simpNF/synTaut declaration linters, consumer probes and approved transitive axioms. The final combined request was 1789228143972754549-schoenflies-9e43b88f (all54 signature/axiom pairs, all75 new FreeTriangle declarations guarded). Module placement changes only imports and modification notices. Final production request1789229595852836547-schoenflies-fb0bcf52 passed in Slurm13781140: all three final module sources freshly compiled without diagnostics, followed by47 exact public/consumer signature and standard-axiom pairs, stock declaration linters over all imported vendor declarations and current consumers, and approved-axiom guards over that entire declaration set. Root independently matched all eight source/configuration/harness hashes and inspected every readback. PROVENANCE.json records exact result and artifact-log digests. All three leaves are registered in the flat aggregate; this gate is not a full DifferentialGeometry aggregate build.

The native PrePolygonTriangulation bridge additionally exposes a finite Mathlib simplicial complex and an actual TriangleMesh, each tied to closure (Schoenflies.inside P.carrier); the mesh also has frontier exactly P.carrier. All construction mechanics stay private. The private source and native consumer passed as 1789230753512712903-schoenflies-44c8ebc9, with14 signature/axiom pairs and50 guards. The final production public mesh corollary and module placement passed fresh gate1789231441425991048-schoenflies-788bbe3d in Slurm13781140: both new modules compiled silently, followed by12 public/consumer signature-axiom pairs, all-imported-vendor/current stock3 linters and standard-only axiom checks including private declarations. Root matched all ten hashes and read all24 readbacks. Import DifferentialGeometry.External.ClassificationOfSurfaces.PrePolygonTriangulation.

Moise/OneEdgeAttachment retains28 selected upstream declarations, checked as 1789229500842743602-schoenflies-19a31622. The geometric one-edge condition is the exact frontier/triangle intersection equal to the base segment; its deletion theorem retains the actual attaching apex edges and frontier equation. ONE_EDGE_SELECTION.json records exact source provenance. It supplies no remaining-disk assumption or conclusion. Its production import placement passed the same final gate as the native bridge; PROVENANCE.json retains the exact input, result and artifact-log digests.

No duplicate polygonal Jordan proof, surface classification library, shelling theorem or smooth disk filling is included in this selected port.

PrePolygonDeletion provides the native closed-region producer after an actual
one-edge-free triangle is removed. Its sole public engine retains the remaining
polygon's oriented old-boundary and attaching arcs, actual frontier and support
equalities. Import DifferentialGeometry.External.ClassificationOfSurfaces.PrePolygonDeletion.
It does not assume a remaining disk. The original frontier equality and geometric
one-edge condition are essential supplied inputs; geometric free-triangle
selection and the two-edge branch are still separate obligations. The private
source passed 1789232885714420646-schoenflies-24adbd8c; final production gate
1789233891983857661-schoenflies-42a7b73c passed after fresh compilation of the new
module. See DELETION_PROVENANCE.json and DELETION_RECOGNITION.patch.
