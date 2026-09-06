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
| Local Dirichlet variants | codex/dev4 | 017599dd08a1f44cc28e3e2354533eefa0a16c23 |
| Forward uniqueness variant | codex/dev5 | c54a1c36a76ee98f1587a2fcbd314ed07b067097 |
| Whole-flow compatibility variant | codex/dev6 | 154a449c71c298e255753286e2d2915c160051d3 |
| Shared foundation snapshot | codex/dev7 | 15c5244d575e34185fe5a1e2f44b32e259fe3a40 |

The uncommitted dev5 forward-uniqueness file is preserved in its worktree; its initial bytes equal the corresponding dev1 file. Initial dev4-dev7 source differences are covered by dev1. Original worktrees remain intact until all useful content is integrated and verified. No published history will be rewritten.

## Integration

Work on `codex/book14-integration`, based on main. Integrate dev1 and dev2 in dependency-closed layers. Dev1 is a descendant of main but deletes 36 main files, including the Harnack development; those deletions are not approved integration outcomes. Preserve the Chapter 9 source and reconcile its dependencies explicitly. Deduplicate shared ODE, scalar maximum-principle, product-metric, radial-flat, and curvature-algebra APIs. Preserve the single flat root aggregate, and keep namespaces decoupled from directory paths.

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
| Dev1 snapshot removes existing Harnack source | Preserve all main Harnack content and reconcile changed dependencies | Open |

## Parallel work and ownership

One shared public contract and import DAG governs all work. The root integrator owns repository state, shared signatures, root aggregate, final acceptance, commits and pushes. Bounded subagents receive exclusive files or read-only searches. They do not independently weaken headlines, introduce theorem-conclusion packages, create duplicate public objects, edit shared roots, or publish commits. Each mathematical result is independently checked before acceptance. Reassign a slot when its bounded task finishes; do not keep a fixed agent-per-chapter hierarchy.

## Delivery gates

For every dependency-closed layer, build changed modules by module name, build affected dependents after signature changes, inspect the full diff, run `git diff --check`, and checkpoint/push only intended compile-clean source. No new proof debt, comments/docstrings in non-vendored Lean, resource budget overrides, or linter suppression are permitted.

Final acceptance requires every coverage row and regression row to close; every public leaf to be wired in `DifferentialGeometry.lean`; fresh changed-module and root `lake build DifferentialGeometry` evidence; standard applicable syntax and declaration linters; exact headline statements with honest minimal hypotheses; and transitive axiom closure containing only approved foundational axioms. Ordinary build progress is allowed; errors, avoidable warnings, info, traces and tactic suggestions are not. Git archival state is not mathematical evidence.

## Current frontier

- Integration branch created from main; original worktrees preserved.
- Three bounded read-only reviews are examining Chapter 2/4 interfaces, the Dirichlet repair, and Chapter 6/7 acceptance.
- Next: integrate dev1 while preserving all main Harnack modules, reconcile the dev2 overlap, then assign disjoint implementation files on the unified baseline.
