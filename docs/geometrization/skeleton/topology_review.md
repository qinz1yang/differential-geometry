# Current topology changes — September 30, 2026

`GC.Topology` now owns `componentCarrier` and `TorusDecomposition`. `NoCuts.torusDecomposition` is proved. `CompactSurface` extends a dimension-generic compact smooth manifold record while retaining its connectedness requirement. The original `CompactCarrier` is unchanged.

`BoundaryTori.transport`, `RawGraphPresentation.transport`, `GeometricDecomposition.transport`, and `SmoothAssembly.Incompressible.toPiece` are proved. Transport uses actual oriented diffeomorphisms and carries the actual collars, seam maps, orientations, and fundamental-group maps. Geometric-decomposition transport retains its abstract cut carrier and full-interior metrics; it does not need to claim completeness for a restricted finite-time flow metric. AT08 and AT09 are the direct blueprint contracts; AT26 is a separate metric-transfer result.

The original closed raw-graph prime theorem is now a proved corollary of two admissions. Prime existence is the closed oriented Hatcher Theorem1.5 specialization. Graph closure is a separate obligation for a specified `SphereSummand`, which carries an actual oriented finite connected-sum reconstruction and exact equality of the chosen factor. Matveev2007 Proposition2.4.3 was freshly read; its prime-uniqueness dependency is explicit. This is a closed-only split, not RG05's full relative sphere/cap/collar ledger.

The mixed-refinement and prime-graph geometric suppliers remain admitted. Their good-block and Seifert vocabulary, full relative cap data, and GM01–GM06 metric decomposition are not installed. An irreducibility contract was explored in scratch only. Hatcher Proposition1.6's supplied descent proof was read; AT16 assumes hyperbolic-core irreducibility and AT18 explicitly disclaims proving it. Cartan–Hadamard, smooth Schoenflies, cover descent, and pushing a compact sphere/core comparison through a collar must be bound before claiming that supplier proved. No unused irreducibility admission was installed.

Actual ambient injection is load-bearing: injection into a hyperbolic model or an owning piece does not imply injection into an arbitrary assembled target. The Myers hyperbolic-knot warning in the audit is retained as motivation, not as a theorem proved or a newly inspected primary reference here. The proved `toPiece` implication runs in the correct direction, cancelling an injective composite.

For a future Blueprint paragraph, G10's converse should say that an E1 essential geometric decomposition yields a Seifert-or-hyperbolic JSJ description after the appropriate refinement/coarsening comparisons; T²×I is labelled Euclidean, and retained product cuts are allowed. This is a proposed source/category adapter, not a consequence of the tag alone. No Blueprint text was edited.

Current source/Lean evidence is in the improvement report and JSON crosswalk. The following original review is retained verbatim as historical context; its counts, statuses, namespace statements and compilation scope describe the frozen earlier version.

---
# Raw graph presentations and geometric refinement — statement review

This is a sorry-based Lean skeleton against blueprint207, not a claim that graph refinement is formalized. All three new topology modules compile. Three existence theorems use `sorry`; their two endpoint compositions and all geometric definitions are ordinary Lean definitions/proofs. Existing proved files are unchanged. The exact explicit declarations, current Lean locations, source labels/line locators, file hashes, and omissions are in `topology_declarations.json`.

## Mathematical correspondence

`Presentation.lean` defines `GC.GraphManifold.RawGraphPresentation W` on the existing actual `CompactCarrier`. Its finite completed cut components carry genuine ordinary smooth circle fibrations: each has a compact connected smooth surface base, a surjective smooth projection, and smooth local product diffeomorphisms over base neighborhoods, commuting with projection. Base orientability is not assumed. These are the regular-circle-bundle blocks of G01/KL14 Definition1.2, not a purported definition of arbitrary Seifert fibers. RG03 removes exceptional neighborhoods when converting Seifert input; each exceptional solid-torus carrier itself admits an ordinary circle bundle over a disk, although this may change its chosen fibration. No arbitrary exceptional Seifert structure is asserted by our local trivialization definition.

The cut/gluing record has actual paired boundary tori, smooth matching maps, oriented collars, a quotient homeomorphism to W, smooth orientation-preserving quotient maps, an interior diffeomorphism, full two-sided seam charts, and actual external collars with exact reconstruction equalities. Boundary exhaustion is by internal paired ports plus unpaired external ports. A self-pairing may join distinct ports of the same connected cut component; left/right subsets remain disjoint. The current type chooses its external index and markings; preserving an arbitrary separately prescribed index/marking would need an additional comparison in the producer signature.

`TorusCut/Decomposition.lean` separates an actual torus decomposition from incompressibility and geometry. `TorusDecomposition M` uses the same existing quotient, smooth reconstruction, piece ownership, and carrier types as `GeometricDecomposition`. `componentCarrier` restricts the actual orientation and atlas to a connected clopen piece; it does not replace that piece by an abstract group or homeomorphism type.

The first sorry theorem exports the **closed** consequence of RG05: a chosen actual prime decomposition whose same factors are raw graph carriers. The second exports the prime graph consequence of RG05–GM06: essential cuts and complete E1 geometric structures on the actual cut interiors. The real theorem `geometrizes_of_rawGraphPresentation` constructs the unchanged existing certificate from those two producers.

For actual mixed late slices, `HyperbolicOrGraph` labels each precise cut component with either a complete hyperbolic structure on its actual interior, or a raw graph presentation on the actual compact component. The hyperbolic case requires the `hyperbolic` model and inherits the existing finite-volume field; a generic homogeneous model cannot satisfy that constructor. Ambient seam injection is a separate explicit assumption at every torus basepoint. The mixed sorry theorem is the principal AT13/AT16/AT17/AT18/GAU03 endpoint consequence. `geometrizes_of_hyperbolicOrGraph` genuinely assembles the output factors and geometry into the existing certificate.

## Assumptions and corner cases checked

- Actual carriers are compact, smooth, Hausdorff, second countable and oriented through the existing type. No orientability of a circle-bundle base is added.
- Raw graph cuts are auxiliary and may be compressible. No injection hypothesis is buried in `RawGraphPresentation`.
- The mixed theorem demands injection into the actual assembled closed manifold, not merely into a hyperbolic model or one cut block.
- The closed input is connected/nonempty through `ConnectedClosedOrientedManifold`. The raw type also represents disconnected nonempty carriers. Existing `Components.count_pos` excludes the empty carrier; callers must treat an empty family separately.
- Zero torus seams, redundant parallel cuts, and loop edges are allowed. There is no hidden nonempty seam assumption and no canonical JSJ requirement.
- Prime sphere products and spherical/S3 exceptions are included rather than excluded by an irreducibility hypothesis. The source supplies the needed chosen factors and metrics.
- No assertion identifies a capped factor with an embedded submanifold of the original carrier.
- Completeness belongs to the actual capped cut-piece interiors, not to a restriction after sphere puncturing. The existing endpoint's E1 convention requires finite volume only in the hyperbolic case.
- A closed Sol or other torus bundle may retain essential product cuts. The theorem does not require an uncut homogeneous metric or an asserted classification by a model tag alone.
- Primitive meridian/transverse versus fiber-parallel filling and all regularity/period checks remain inside the missing source producers; no separate incorrect universally transverse filling theorem was introduced.

## Deliberate omissions

This bounded skeleton does **not** export RG05's full relative punctured-carrier/cap-ball/sphere-cycle ledger, maps preserving every original prescribed marking, or a comparison to a separately prescribed prime decomposition. It therefore must not be advertised as the full AT13/AT16 Lean interface. Its mixed conclusion is the unchanged endpoint certificate with chosen final cuts and actual reconstruction. The detailed intermediate models, filling lemma, good-block construction and individual GM01–GM05 metric calculations still require more granular future statements/proofs. The JSON lists these omissions.

## Sources actually consulted

Blueprint207A: G01–G05 at lines8517–8588; RG01–RG06 at9315–9579; GM06 at10378–10431. Blueprint207B: AT13–AT18 at11895–12036; GAU03 at12459–12497. These bodies/proofs were read in this task. Source checks169–171 were read and reused: Matveev second edition2007 Definitions2.4.1/Propositions2.4.2–3 printed84–85/PDF96–97 and Example6.4.14 printed248–249/PDF258–259; archived Hatcher1999/2000 Proposition2.1 printed24–26/PDF25–27; Martelli Version4 September2025 circle-bundle/filling passages10.2.1–5 printed312–314/PDF320–322 and10.3.1–8 printed316–318/PDF324–326. Exact source hashes and the GM01–GM05 metric/Lee correction evidence are preserved in `GEOMETRIZATION_BLUEPRINT/research/graph_realization_2026-09-27/source_checks_revision171.json`.

KL14 Definition1.2 printed8/PDF3 correspondence reuses the recorded revision56 source check (archive SHA256 `7a860b4dd95b35fe33b06bf040100ec243d72c80528d927f4763391aaf79cb6e`). No new primary-source full reading or fresh erratum clearance is claimed. The archived Scott erratum retrieval limitation remains. An attempted fresh local extraction could not run because this shell has neither pdftotext nor Python PDF libraries; the checked source record and actual blueprint bodies suffice for this unchanged regular-bundle definition.

## Verification and second reading

Ran `LEAN_NUM_THREADS=2 lake build DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Refinement`; all three topology modules compiled. Build log: `.lake/gc/skeleton-topology-build.log`. It reports exactly the three intended sorry declarations; unrelated inherited style warnings were replayed. This is not a proof of those three theorems. No whole-root build was run by this agent.

The collapse-skeleton agent independently reread both modules and found no blocking semantic mismatch, specifically checking local circle products, nonorientable bases, boundary exhaustion/markings, and separation of ambient incompressibility. The root agent independently reread the principal endpoint signatures. The generic component carrier and torus decomposition were then moved into their mathematical home `TorusCut/Decomposition.lean` without changing namespaces or any statement. A final rereading confirmed the raw/essential and metric/topological distinctions after this split.

Conversely, I independently reviewed `CurvatureScale.lean`, `CuspBoundary.lean`, and `GraphManifold.lean` against selected BBR03 (207B10592–10620), LC88, and the retained closed route. The later active statement uses r<Rp, distance>10, whole-ball derivatives through K, a C^{K+1} cusp map with relative C^K metric error, and ds²+e^{-s}h with curvature−1/4; the skeleton preserves these. K and A precede one threshold and all carriers, the common-threshold proof has the correct monotonicity directions, and Fin0 component families are valid. The radius∞ branch is retained and must use the nonnegative-curvature classification inside the missing producer. The boundary theorem was strengthened after this review: it now consumes the prescribed `NearlyCuspidalBoundary` and returns an explicit equivalence of boundary indices with equality of actual torus subsets. This preserves the supplied component labels, while correctly avoiding an identification of finite-C cusp parametrizations with smooth graph collars. The generic common-threshold corollary intentionally forgets that additional witness.
