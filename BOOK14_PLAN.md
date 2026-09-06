# Book14 formalization plan

The active goal is the complete formalization of Chapters 2, 3, 4, 5, 6, 7, and 9 of `book14.tex`, including their necessary mathematical dependencies. `BOOK14_COVERAGE.md` is the source-to-declaration acceptance inventory. The repository authorities are `AGENTS.md`, `NAMING.md`, and `STRUCTURE.md`.

## Scope and evidence

The original supplied bytes have SHA-256 `f88233190c4efe6631beade0150bb4bc37b7df32565a38da0496030ffb835c08` and are preserved outside the repository in the task artifact directory. Only trailing whitespace was normalized for the repository diff gate; source line numbers and mathematical content are unchanged. The tracked source snapshot has SHA-256 `ff3e8df5e43995554e641d0a31ba7caa85186eb5ba281c8679056f5a9a079abf`. The initial inventory has 148 explicit definition, theorem, lemma, proposition, corollary, or example environments. Load-bearing identities in prose and unboxed developments must be added as they are extracted. An alternate proof of a headline does not discharge a separately stated textbook theorem such as the Kazdan-Warner identity.

Each inventory row must eventually identify the exact fully qualified Lean declaration(s), hypotheses and conclusion correspondence, natural topic home, dependencies, and fresh compiler, linter, and axiom evidence. The default status is unverified, never complete by source-grep or by a file name. Conditional engines are useful but do not count as closed classical headlines.

## Preserved source snapshots

| Role | Worktree branch | Initial commit |
| --- | --- | --- |
| Integration base and Chapter 9 | main | 3400ed78ff97a3d7cb10cec73f66e598225e4036 |
| Chapter 5 and shared foundations | dev1-clean | 752f3f97786839bb16def363233b55bcae672485 |
| Chapters 6 and 7 | dev2 | a9a8b02f7dfc4a619eb4825e9ec1f362cc93e105 |
| Chapter 9 historical worktree | dev3 | c189435223cd1d0cd767b13504edebfd895250bc |
| Historical Dirichlet spectral foundations, not checked out | dev1-clean-latest | f29eb244e4af286367f99446ed2615710aac7f60 |
| Local Dirichlet variants | codex/dev4 | 017599dd08a1f44cc28e3e2354533eefa0a16c23 |
| Forward uniqueness variant | codex/dev5 | c54a1c36a76ee98f1587a2fcbd314ed07b067097 |
| Whole-flow compatibility variant | codex/dev6 | 154a449c71c298e255753286e2d2915c160051d3 |
| Shared foundation snapshot | codex/dev7 | 15c5244d575e34185fe5a1e2f44b32e259fe3a40 |

The uncommitted dev5 forward-uniqueness file is preserved in its worktree; its initial bytes equal the corresponding dev1 file. Initial dev4-dev7 source differences are covered by dev1. Original worktrees remain intact until all useful content is integrated and verified. No published history will be rewritten.

## Integration

Work on `codex/book14-integration`, based on main. Integrate dev1 and dev2 in dependency-closed layers. Dev1 is a descendant of main but deletes 36 main files, including the Harnack development; those deletions are not approved integration outcomes. Preserve the Chapter 9 source and reconcile its dependencies explicitly. Deduplicate shared ODE, scalar maximum-principle, product-metric, radial-flat, and curvature-algebra APIs. Preserve the single flat root aggregate, and keep namespaces decoupled from directory paths.

The additional local historical branches were inventoried after missing imports exposed their relevance. `dev1-clean-latest` and `dev1-clean-legacy` retain 19 source files missing from the original checked-out integration inputs: 18 Dirichlet analytic developments and the flow time-shift file also supplied by dev2. Their shared files are older variants of current canonical APIs; integrate useful missing mathematics and reconcile consumers explicitly, without reverting the canonical eigenvalue indexing or reintroducing deleted Harnack content. `dev1-clean-ch5` has no additional missing files.

## Shared dependency forest and order

1. **Common bundle, metric, connection, and algebra layer.** Fix the curvature sign, final-slot swap, sectional versus trace normalization, trace-to-scalar formula, Laplacian convention, adjugate reaction, smooth parameter dependence, and tensor-to-operator transport.
2. **Chapter 4.** General metric freezing; smooth inverse bundle isometry; pullback metric connection and induced connections; first derivative, Hessian, rough-Laplacian naturality; actual raw curvature evolution; four-slot time derivative and Ricci cancellation; intrinsic three-dimensional operator equation; gauge, scaling, and nullspace covariance. Derive equations from actual flows, not assumed component evolution.
3. **Chapter 2.** Parallel nonempty closed convex families; transport-based local products and fiber distance continuity; geodesic support test; ODE invariance from every starting time implies the inward normal inequality; uniform local Lipschitz bound; strict expanding tube and first contact; drift, ODE-to-PDE, and associated-bundle headlines. A global frame, globally flat charts, zero-in-convex-set assumption, or caller-supplied support sections must not replace the book hypotheses.
4. **Chapter 3.** Reuse the existing closed-flow pinching proof and dev1 consequences. Align the trace-normalized primary statement, normalized corollary, positive-time estimate, blow-up ratio, and closed-ancient nonnegativity. Audit the fixed spectral region, polynomial reaction, ODE invariance, time change, and parabolic scaling.
5. **Chapter 5 local and fixed-time development.** Repair the empty-domain hypothesis; construct genuine scalar Dirichlet solutions and prove positivity on suitable nonempty relatively compact domains; close Ky Fan rank spreading, spatial rank constancy, finite rank-stable intervals, smooth kernel, spatial parallelism, precise kernel-motion law, and temporal constancy under reaction annihilation. Produce all curvature-specific inputs from Chapter 4, exclude rank two, derive the tangent line without orientation, and prove complete fixed-time universal-cover splitting.
6. **Chapter 6, independently of the Chapter 5 global-time upgrade.** Verify and close covariance, weighted identities and integration by parts, sharp scalar lower bounds, potential growth/properness, potential-field completeness, canonical self-similar flow and the natural flow interface, scaling/conjugate-heat/converse laws, models, CLY, and Munteanu-Wang.
7. **Chapter 7 common classification.** Use Chapter 5 fixed-time splitting and Chapter 6 to close the nonnegative-curvature classification: Gaussian, rank-one cylinder with potential splitting and the complete surface classification, and positive spherical branch via Munteanu-Wang and anisotropy. Preserve metric and potential equalities in covering maps, classify deck groups and potential-preserving cylinder quotients, and expose orientation/topology consequences. Prove the separately stated Kazdan-Warner identity as its own reusable theorem.
8. **Chapter 7 unrestricted and singularity-model siblings.** Prove complete localized Hamilton-Ivey without a global curvature bound or initial lower bound, then complete-ancient nonnegativity and unrestricted complete shrinker classification. Independently use closed-flow pinching and pointed blow-up convergence for the singularity-model wrapper. Neither wrapper may smuggle its nonnegativity conclusion into a hypothesis or erase the identifying map.
9. **Chapter 5 whole-flow upgrade.** Verify or complete bounded-curvature complete short-time existence and forward uniqueness. Derive rank-mode persistence, one fixed physical parallel line and one-form, and one fixed surface/diffeomorphism for the whole interval. Prove that the surface factor is a complete positive-curvature Ricci flow. A separate product at each time or an assumed common product witness is insufficient. Chapter 7 does not wait for this upgrade.
10. **Chapter 9 preservation and acceptance.** Verify exact P/M evolution, finite test jets, block evolution, Gram squares, strict rank-one support, proper slab barriers, shifted/finite-origin/compact matrix Harnack, trace/optimization/integrated forms, and ancient limits. Include the necessary Chapter 8 all-slot heat commutator and positive-slab Shi estimates in the proof closure, without expanding scope to all of Chapter 8.

## Open mathematical regression rows

| Finding | Required repair and evidence | Status |
| --- | --- | --- |
| Universal Dirichlet hypothesis forces nonempty interior even for the empty compact set | Replace the domain quantifiers with a natural sufficient family; construct solutions from geometric/PDE data; compile the empty-domain regression and actual consumers | Open; contradiction independently compiled before integration |
| Rank/trichotomy engines accept derived spatial rank, parallel kernel, null reaction, or global rank mode | Produce these properties from the actual evolution under the intended hypotheses | Open |
| Whole-flow product interfaces assume a common product and quantify over the whole real line | Produce one fixed product from the flow and restrict conclusions to its controlled time domain | Open |
| General bundle WMP asks for support sections, distance continuity and zero membership | Derive the geometric inputs and cover arbitrary nonempty parallel closed convex families with drift | Open |
| Component curvature transport can assume the evolution or scalar-Laplacian bridge | Derive the intrinsic fixed-bundle equation and naturality from real curvature and connection constructions | Open |
| Unrestricted complete three-shrinker classification lacks the localized nonnegativity route | Prove the exact complete localized Hamilton-Ivey estimate and its ancient/canonical-flow consequences | Open |
| Surface classification via another proof route does not prove Kazdan-Warner | Track and prove the standalone identity stated in Chapter 7 | Open |
| Dev1 snapshot removes existing Harnack source | Preserve all main Harnack content and reconcile changed dependencies | Repaired: byte-preserved source, fresh full build and all 23 module axiom/linter gates passed |
| Dev1 has 31 unregistered new modules with no build artifacts | Register every imported new leaf, build the actual Dirichlet, volume-density and time-energy developments, and resolve any exposed source failures | Repaired: all leaves registered and the actual formerly unwired source rebuilt; canonical indexing and H1-density errors repaired |

## Parallel work and ownership

One shared public contract and import DAG governs all work. The root integrator owns repository state, shared signatures, root aggregate, final acceptance, commits and pushes. Bounded subagents receive exclusive files or read-only searches. They do not independently weaken headlines, introduce theorem-conclusion packages, create duplicate public objects, edit shared roots, or publish commits. Each mathematical result is independently checked before acceptance. Reassign a slot when its bounded task finishes; do not keep a fixed agent-per-chapter hierarchy.

## Integration acceptance queue

| Layer | Exact source state | Verification available | Remaining integrated gate |
| --- | --- | --- | --- |
| Main Harnack preservation | All 36 deleted main files restored byte-for-byte; second Ricci derivative regularity reunited with dev1's Ricci-sharp regularity | Reunited regularity source compiled silently against dev1 imports; Harnack folder has zero diff from main | Passed full root and all preserved-module axiom/linter gates |
| Pullback metric compatibility | New `Geometry/Connection/PullbackMetric.lean` | Exact source compile, applicable linters, approved axioms | Passed full root and all-module axiom/linter gates |
| Closed-interval linear ODE | New `Analysis/ODE/Flow/ClosedInterval.lean`; Banach existence, uniqueness, joint parameter regularity, and produced smooth solutions | Exact source compile, applicable linters, all four approved axiom closures | Passed full root and all-module axiom/linter gates |
| Direct rank propagation | Generalized local spatial barrier; continuous scalar drift pairing; three Ky Fan/rank propagation engines using actual evolution | Exact promoted ScalarStrong, MetricFamilyRegularity, InitialData and RankSpreading sources compiled in isolated overlay; applicable linters and all five approved axiom closures | Full dependent/root and all-module axiom/linter gates passed; actual-flow producers and minimal assumptions remain mathematical work |
| Canonical soliton flow | New dev2 `Soliton/Solution.lean` with actual IsSolutionOn and completeness | Module build, applicable linters, approved axioms, Gaussian interval consumer | Promoted with generic constructor in Solution/Basic; unified full build and all-declaration gates passed |
| Dev2 source reconciliation | Seven resolved source conflicts and aggregate import union | Combined product, pointwise Laplacian, Strong, ScalarStrong, and preserved Harnack source compiled together | Unified 12940-job full build and fresh 206-module declaration gates passed |

Temporary regularity engines still expose spectral continuity and compact operator/reaction bounds; those inputs must be derived from genuine joint bundle regularity. Their nonzero base-dimension restriction and assumptions outside the controlled time interval are explicit generality review items, not accepted properties of the final classical theorem.

## Delivery gates

For every dependency-closed layer, build changed modules by module name, build affected dependents after signature changes, inspect the full diff, run `git diff --check`, and checkpoint/push only intended compile-clean source. No new proof debt, comments/docstrings in non-vendored Lean, resource budget overrides, or linter suppression are permitted.

Final acceptance requires every coverage row and regression row to close; every public leaf to be wired in `DifferentialGeometry.lean`; fresh changed-module and root `lake build DifferentialGeometry` evidence; standard applicable syntax and declaration linters; exact headline statements with honest minimal hypotheses; and transitive axiom closure containing only approved foundational axioms. Ordinary build progress is allowed; errors, avoidable warnings, info, traces and tactic suggestions are not. Git archival state is not mathematical evidence.

## Current frontier

- The source contract is committed and pushed on the integration branch. The verified dev1 integration preserves the 36 deleted main files and the original worktrees, and registers all 31 previously unwired dev1 leaves.
- Missing Dirichlet spectral roots, stale canonical eigen-index consumers and the genuine H1-density construction have been repaired. The 10045-job common-foundation build passed; the 12828-job full aggregate and all-declaration audit of 262 modules also passed with zero diagnostics.
- The empty-domain contradiction is repaired by a nonempty connected-interior condition at the three affected interfaces. Genuine classical Dirichlet existence and actual-flow rank producers remain open, so the classical rank theorem is not yet accepted.
- General connection forms, local ODE invariance, arbitrary-interval metric freezing, intrinsic Ky Fan continuity, curvature-reaction regularity, normal cones and the convex support engine with drift are integrated. The next geometric producer is actual parallel transport and its use to construct distance/support fields.
- Exclusive continuation tasks are general-connection transport; actual Dirichlet coefficient operators and weak-solution regularity; and the independent Kazdan-Warner development. Root owns integration and the actual Ricci-flow metric-freezing interface.
- Dev2 source reconciliation, complete surface metric/potential classification, canonical soliton flow and conformal metric/vector-field APIs are integrated and have passed the unified gates. Remaining textbook statements still require individual source correspondence and actual-producer acceptance.


## Verified integrated foundation checkpoint

At checkpoint `c14c70ba48e49a30d88e3f8ad48be48b9439049e`, the unified dev1 merge registers every recovered leaf, preserves the main/dev3 Harnack developments, and has passed a 10045-job common-foundation build. The full `lake build DifferentialGeometry` gate passed 12828 jobs, including formerly unwired Dirichlet modules and the Matrix/Trace Harnack chain. After removing one duplicate root import and the unused completeness assumptions in TimeH1Energy, the final affected-dependent and aggregate gate again passed 12828 jobs with zero diagnostics.

The current 237-module source review finds no proof debt, resource-budget overrides, linter suppressions or diagnostic commands; its only comment matches are required retained copyright headers. `git diff --check` is clean. All 262 targeted modules passed full public/private/generated-declaration linters (excluding only the two documentation-presence linters) and transitive-axiom checks allowing only propext, Classical.choice and Quot.sound. These cover all 237 changed/new leaf modules, all 23 preserved Harnack modules, RankOneSupport and SlabExhaustion. Exact source hashes were rechecked after the audits. Every changed leaf is registered exactly once. These gates certify this integration checkpoint; outstanding source correspondence and classical-producer rows remain open.

New integrated mathematics includes the normal cone and unique metric projection/support theorem for complete convex subsets of arbitrary real inner-product spaces, the actual local-ODE inward-support lemma, arbitrary-interval metric freezing (including initial endpoints and singletons), general connection forms and their coordinate-change/regularity laws, intrinsic bundle Ky Fan continuity, uniform curvature-reaction Lipschitz bounds, and the support-form convex maximum-principle engine with drift and positive-time spatial smoothness. The weak maximum principle's actual parallel-transport support producer is still being constructed.

The repaired Dirichlet chain keeps the canonical resolvent eigen-index representation and reconstructs a genuinely H1-dense smooth sequence before the L2 Gram-Schmidt procedure. It proves both H1 and L2 density, restoring real integrated weak existence and the nonautonomous abstract maximal-regularity assembly. It does not yet supply the classical local Dirichlet solution: coefficient-derived operator bounds, short-time perturbation control, reverse elliptic Sobolev embedding, pointwise representatives, boundary traces and positivity remain explicit dependencies. Historical `SmoothEmbedding` only proves interior-supported smooth functions belong to all spectral Dirichlet spaces; its name does not certify the needed reverse implication.

The dev2 surface-classification layer is frozen with actual arbitrary-rate Euclidean, round-sphere and real-projective-plane metric/potential identifications and pairwise exclusivity. General conformal rescaling has also been proved. The independent Kazdan-Warner identity remains open. A candidate spectral route first proves the genuine two-dimensional Rellich identity and weighted eigenfunction-square cancellation, then requires a produced heat kernel, justified spectral/integral interchange and the uniform diagonal curvature coefficient with a controlled remainder. Those analytic inputs are still open. Uniformization is another possible route, not an assumed witness or a completed dependency.


The Dirichlet continuation uses genuine H1-zero-boundary to H-minus-one and L2 to H-minus-one coefficient operators, and H2-intersect-H1-zero-boundary to L2 only where justified. Arbitrary moving metrics do not preserve every higher-order compatibility condition encoded by a fixed reference Dirichlet spectral scale. Classical smoothness will therefore use local parabolic regularity of the actual weak solution and a separate boundary-trace/barrier argument; an unconditional all-orders fixed-scale mapping assumption is forbidden.


## Frozen continuation queue

The next controlled integration window contains two dependency-closed Dirichlet layers (static spectral/energy identifications and genuine low-order coefficient operators), general covariant differentiation along curves, parameterized parallel transport and metric compatibility, the actual Ricci-flow gauge-velocity and regular-interval isometry producer, and the prepared dev2 merge. The latter includes the complete surface classification, canonical soliton flow, conformal metric/vector-field APIs and the genuine two-dimensional Rellich/eigenfunction cancellation. Each layer has isolated source, declaration-linter and axiom evidence and is still required to pass the unified gate after promotion.


## Verified second integration gate

The actual dev2 merge is pending on the integration feature branch. Its seven shared source conflicts were reconciled with the precompiled resolutions: retain the stronger rank/radial-flat/Hessian APIs, combine the product and pointwise operator APIs, and preserve the interior barrier and rank consumers while integrating dev2's noncompact scalar maximum principles. No source deletion is staged.

All 17 frozen dev2 files have been promoted, including the surface classification, canonical-flow bridge, conformal geometry, Rellich identity, naturally placed spectral summability and generalized canonical eigenfunction. The generic `isSolutionOn_of_reg` constructor was moved intact from compactness into Solution/Basic. The three frozen Dirichlet layers (18 files) and the latest along-curve, metric-compatibility, parameterized local-transport, time-derivative and actual Ricci-gauge layers are also promoted.

The flat aggregate wires all 180 new/changed leaf modules, including 34 original dev2 leaves absent from its aggregate. The 11937-job named-module gate and the separately repaired CurvatureOperatorBounds module passed with zero diagnostics. The final full aggregate gate passed all 12940 jobs with zero diagnostics. A fresh audit after this build passed all 206 targeted modules: all 180 changed/new leaves, all 23 preserved HamiltonHarnack modules, RankOneSupport, SlabExhaustion and Exterior/Leibniz. Every public, private and generated declaration passed standard declaration linters except the two documentation-presence linters, and its transitive axioms contain only propext, Classical.choice and Quot.sound. All source hashes match the audited snapshot, every changed leaf is registered exactly once, and git diff --check is clean.

Three integration repairs were required: remove the unused CompactSpace input from a private SurfaceMorse lemma; restrict the existing global wedge notation to the differential-form scope so that logical conjunctions retain their meaning after reunited imports; and update the preserved curvature-operator lower-bound proof to consume the canonical least-eigenvalue theorem while preserving its public signature. The 23 HamiltonHarnack files remain byte-identical to main. This certifies the integration layer, not the still-open classical headlines or source-correspondence rows.

The moving-mass weak existence producer now derives uniform coefficient bounds from genuine joint regularity and outputs the same weak solution, continuous L2 representative, a.e. identification and original initial datum. This remains weak existence: classical representatives, boundary continuity/barriers and positivity are open. The next real weak-derivative bridge uses H1 completion and chart weak derivatives, not a raw-fderiv predicate mislabeled as a weak equation.


## Next producer layers

The actual H1 representative now has a frozen chart Sobolev bridge and quantitative norm bounds, following the frozen all-H1 Green identity and drift-form identification. The local chart Lp comparison was generalized to measurable functions and arbitrary 1 ≤ p < ∞, so convergence is tied to the same H1ToLp representative by genuine convergence-in-measure uniqueness. Actual iterated weak-derivative Lp operators and their completion/time-L2 consumers are being checked. Conversion of the moving-mass weak equation into its local parabolic form remains open.

General-connection parallel transport has frozen arbitrary-interval uniqueness, actual closed-segment piecewise gluing, and actual parallel-section joint smoothness on arbitrary order-connected time sets. The gluing proof derives matching coordinate derivatives from the same connection, curve and endpoint values; it assumes no smoothness of the glued section. The same produced global transport and its forward/inverse joint smoothness are the current continuation.

The actual spectral heat kernel has frozen positive-time absolute convergence, symmetry and joint continuity, weighted integral/spectral interchange, a genuine L2 heat-semigroup representation, convolution, full time-and-two-space-variable joint smoothness, the actual heat equation, and the two-dimensional conformal weighted-diagonal cancellation. The uniform diagonal curvature coefficient and controlled remainder needed for Kazdan-Warner remain open; the continuation starts with genuine parameter-volume-density regularity and the actual normal-coordinate Ricci coefficient.

Root has frozen total-space regularity from actual Hom sections on their natural projection-preimage domains and the parallelism of the actual equivalence section for the induced Hom connection of its pulled-back connection. The composition Leibniz layer and actual endomorphism conjugacy, Hessian and rough-Laplacian formulas have passed isolated source and all-declaration linter/axiom gates. They retain actual pulled connections, derive the inverse regularity, and include zero-dimensional bases. The Hessian primary permits any base connection; the Laplacian is its finite-trace corollary. Tensor/exterior identifications remain open.
