# Geometrization team plan

Prepared September 28, 2026 for Ziyang Qin, Bennett Chow, Yuan Liao, Peng Lu,
and Ayush Khaitan. Current scope: revision207 wraps up the blueprint and the user-requested
module placement. Further proof work awaits discussion. The collaboration
plan below is adaptable guidance for Ziyang and the team, not an active coding
assignment.

## Organizing principle

Ziyang leads the project and controls integration and the largest parallel coding
queue. Do not divide the theorem into five equal shares. Feed his compute a
large supply of independently specified, reviewable proof tasks, while the other
four members own substantial developments and keep the mathematical interfaces
correct. Useful throughput is accepted producer-to-consumer chains, not lines of
Lean or numbers of named theorems. No numerical compute allocation is assumed.

Proposed starting responsibilities, subject to the team's preferences:

| Member | Substantial coding contribution | Coordination contribution |
|---|---|---|
| Ziyang Qin | Largest proof queue across all available lanes, especially the analytic critical path | Project lead; integration decisions, shared interfaces, compute and cache infrastructure |
| Bennett Chow | Flow-control and geometric-analysis adapters; difficult source-to-Lean contracts | Blueprint/source review, mathematical adequacy, prioritizing blockers with Ziyang |
| Yuan Liao | Reusable API design, difficult transports and producer/consumer adapters | Lean architecture and integration review; turn recurring failures into reusable lemmas |
| Peng Lu | An independently owned analytic or collapse packet chosen after interface review | Second mathematical/proof reviewer on another lane |
| Ayush Khaitan | An independently owned reconstruction, topology or geometry packet chosen after interface review | Second interface/proof reviewer on another lane |

These are recommendations, not assignments already accepted by the members.
Bennett, Peng and Ayush are not restricted to reviewing; each should own complete
coding packets. Yuan should not become the sole person who fixes everyone's
integration problems. Ziyang can delegate routine integration to rotating
integrators while retaining authority over shared contract changes.

## Sequence and completion criteria

1. **Shared checked baseline — this delivery.** Promote the successful pilot
   sources to a normal Lake library, preserve PC types and source provenance,
   provide a small real flow interface with downstream checks, establish the
   build/axiom gate, and publish the team plan on a new private branch. See
   `STEP1_REPORT.md` for actual checks and limits.
2. **Review the contracts and claim the first packets.** Ziyang and Yuan review
   the shared Lean surface; Bennett leads the backward check from GA23/GA22/LP12.
   Extract exact statements from the current blueprint rather than inventing new
   abstract output records. Review the global analytic and marked reconstruction
   interfaces first. Every released coding packet has one owner, precise
   parameters/quantifiers, a source record and a compiling consumer. Task cards
   here are interface-review work, not approved theorem specifications.
3. **Start independent proof lanes.** Ziyang fills the largest queue of ready
   tasks; the rest of the team claims bounded producer chains. Work on global
   flow control, marked reconstruction, local-collapse foundations, and endpoint
   interfaces concurrently where dependencies permit. Integrate small proofs
   promptly; avoid isolated chapter-sized branches.
4. **Connect the analytic and topological applications.** Local packets feed
   static collapse; controlled flow feeds persistent hyperbolic regions and the
   actual thin complement. Persistent regions feed ambient cusp
   incompressibility. Relative graph refinement and complete geometric witnesses
   can develop independently, then attach to the actual complementary carriers.
5. **Close the endpoint and audit it.** Compose both late-thick/thin and terminal
   exceptional branches with actual marked reconstruction of the initial
   manifold. Audit the final quantified theorem, normalization, essential cuts,
   all required model geometries, whole-interior completeness and retained volume
   policy. Run the dependency/axiom gate on the actual endpoint; a passing build
   of conditional packets is not completion.

The checked endpoint, raw-flow interface, bounded history consumers and
standard-factor producer already implement parts of steps2–5. The remaining
producer work is future work. Their ordering is a dependency/risk judgment, not a
time estimate. Interface discovery may change the queue; record why rather than
silently changing the endpoint.

## First work queue

`tasks/*.json` records proposed packets, dependencies and exclusive write areas.
Cards remain unclaimed. Some exact statements and consumers now exist; the
current cards and endpoint audit identify their scope. Assign new proof work
only after the interface review described in each card.

| Packet | Starting point | Required output and important restriction |
|---|---|---|
| T01 | Existing endpoint and DAG | Backward field-by-field endpoint census, including actual carriers and both alternatives; no claim that all dependencies are already semantically audited |
| T02 | General finite histories and raw tower | Globally admissible flow/profile producer with the exact common quantifiers; raw coherence alone is insufficient |
| T03 | Actual single-event geometry and marking | Full marked finite-history reconstruction, including ports, multiplicities and cycle factors; group ancestry alone is insufficient |
| T04 | Chapters 3–4 and 13 | Actual local-collapse packets using the written finite-regularity route and audited PC reuse |
| T05 | Chapter 14 | Actual compatible fibrations and static collapse, including markers, sheets, properness, corners and simultaneous parameters |
| T06 | Chapters 8, 12 and 13 | Persistent hyperbolic regions and precise thin-complement estimates on the actual controlled flow |
| T07 | HG10–HG15 / AT01 | Ambient incompressibility via the global area function through surgery, not merely injection into the model |
| T08 | Chapters 5–7, AT13/AT16, GA06 | Relative graph refinement and all required complete geometric model witnesses, retaining boundary markings |
| T09 | Outputs above | Actual marked initial-manifold endpoint, including terminal exceptional cases |

Use revision207's current-view overlay and consolidated DAG. Historical202
frontiers retain their original evidence scope. The
small task register is only scheduling metadata; its edges are delivery gates,
not an exhaustive theorem dependency claim. Suppliers can be developed against
reviewed interfaces before all their dependencies have implementations, but a
conditional proof remains conditional until the actual producers are connected.

## Branches, claims and integration

- Start from the agreed integration commit. This delivery is on
  `codex/geometrization-team-foundation`; the existing baseline201 branch remains
  the historical checkpoint. Ziyang chooses when to merge and which branch will
  be the continuing integration branch.
- Use `gc/<owner>/<task-id>-<short-name>` branches and one worktree per active
  human/agent task. Push them only to the private development repository. Never
  run multiple agents that edit the same checkout or claim the same files.
- Record a claim in the packet's own JSON and have it land on the integration
  branch before launching overlapping work. A person can coordinate many leaf
  tasks, but each leaf has one writer and one distinct reviewer. Claim collision
  is resolved by the integrator, not by timestamp guesses.
- Split a large packet into child cards before dispatch. Each child records the
  exact parent interface commit, read dependencies, allowed write files,
  theorem statement, source locators, consumer and completion check. Root
  imports, Lake pins, shared interfaces and the mathematical DAG have one
  integrator; leaf agents request those edits in their PR.
- Every PR gives a source-checked contract comparison and a real downstream
  consumer. Review mathematical strength separately from elaboration and axiom
  results. Kernel checking does not detect an inadequately specified theorem.
- Merge supplier and consumer changes together when an interface changes.
  Rebase dependent branches early; retain a short compatibility adapter where
  useful. Toolchain or PC upgrades are separate project-wide migrations.
- Prefer incremental local checks, then the full team target before merging.
  Reuse trusted caches keyed by source, options, toolchain and platform. Ziyang's
  infrastructure is the natural place for shared warm builds; access and runner
  provisioning still need the repository administrator. Do not upload private
  caches or sources to a public service.
- Track blocked consumers and integration rework. If several agents duplicate
  work or repeatedly miss a shared interface, fix the interface/queue before
  increasing concurrency. No fixed number of agents or review turnaround is
  imposed by this plan.

## Mathematical acceptance rules

Use the accepted PC foundation directly. Do not recreate manifolds, metrics,
curvature, surgery histories or fundamental groups under unrelated toy types.
Keep metric/domain/normalization choices visible. A `Prop` field containing the
desired conclusion is a consumer assumption until a genuine producer is proved.
Do not turn a difficult implication into a typeclass assumption and count the
result as unconditional. Preserve empty, disconnected and zero-event cases.

No `sorry`, new mathematical axioms, unsafe proof declarations, or kernel-check
bypasses in the accepted team library. The gate checks transitive axioms of
declarations owned by the library and its checks against `propext`,
`Classical.choice`, `Quot.sound`. Standard classical axioms are allowed; new
analytic premises require mathematical review even if they are ordinary theorem
hypotheses and hence invisible to an axiom audit.

Every important contract records the exact source version, theorem and proof
locators, corrections, quantifier order, finite regularity, boundary conditions,
normalization and producer-to-consumer transports. Written blueprint proofs,
inspected PC declarations and checked Lean proofs are different evidence levels.

The current blueprint is master207.tex/A.tex/B.tex. The standard-factor leaf
is proved, while controlled late production and the general theorem remain
open. The current handoff supersedes obsolete next-step descriptions.

All live modules belong to their subject homes under DifferentialGeometry,
following NAMING.md and STRUCTURE.md. There is one flat root aggregate.
MODULE_PLACEMENT.json maps the old paths; the accepted PC leaf sources and
dependency pins are preserved. Push only to Ziyang's private development repo.
