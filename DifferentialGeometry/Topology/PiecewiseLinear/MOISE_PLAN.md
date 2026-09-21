# Moise 光滑化（拓扑三维流形 → 兼容光滑结构）阶段计划

> Claude takeover (2026-09-19 UTC). Owner stopped all Codex usage.
> Read HANDOFF_CLAUDE_20260919.md and .lake/claude-handoff-state-20260919.json first.
> All five Codex tasks and their compiler leases stay paused; automation moise is
> PAUSED and must not be resumed. Batch64 is now independently accepted and
> committed; see section 100 and .lake/verified-sixtyfourth-lane-delivery-20260919.json.

统一记录本任务的目标、复用审计、证明路线、阶段与验证。其他文档只引用本文件，不另开状态表。
日期均为绝对日期。路径省略 `DifferentialGeometry/` 前缀时指本库源码树。

## Current plan after source audit and owner build stop (2026-09-19 UTC)

The classical route is retained; the project remains in core proof construction.
[The source/book audit](ROUTE_AUDIT_20260919.md) records the evidence. There are
two independent missing inputs: general PL approximation and compact PL
three-manifold smoothing. Conditional Endgame and Smoothing theorems supply
neither. Compactness suffices for the final smoothing consumer; approximation
must cover noncompact chart overlaps and positive error tending to zero at
their boundary.

This is the current execution plan. Sections 2 and 6 retain dated baselines and
verification history; their old ownership, running-build and source-style
statements are not current instructions. The six subject labels in the detailed
Phase 3 table are mathematical categories, not six active tasks.

### Owner risk decision: prioritize 25.2 at delivery boundaries

[The Loop Theorem risk plan](LOOP_THEOREM_RISK_PLAN_20260919.md) now governs
next-round allocation. F takes actual projected-disk relative normalization;
M304 takes upstairs Lemma 2/L2 surgery; h takes whole-branch two-sheet charts;
E3 takes the actual sphere-base/tower-interface assembly. S keeps independent
compact smoothing. These four changes occur only at each task's next explicit
delivery or genuine blocking handoff. Current active rounds remain intact;
M304 has now moved to upstairs L2 at its complete e8dc3d37d delivery; h/E3
changes still await their own boundaries. S continued at its e24808bce delivery.
No new task, subagent, extra lane or compiler slot is created.

The audit's projection insight is adopted as the primary route. Existing
projection, finite spherical boundary-domain and inward-push producers are
reused. The corrected orientable Moise252 contract is already accepted.
Global normal crossings, whole-branch geometry, actual L2 surgery, branch
count/descent and exact tower assembly remain the priorities. Tower vertex
collision complexity is not normal-disk branch complexity. The conditional
304 endpoint does not remove the other outstanding section34 inputs.

### Latest live frontier (2026-09-19, protected-polyhedron relative general position accepted)

This snapshot and the latest integration-handoff sections supersede dated
paragraphs below. The resumed stage has no new deadline. Five existing tasks
keep one lane each; F/S/M304 use Astra max and h/E3 use Sol max.

| Lane | Independently accepted frontier | Current mathematical gate |
|---|---|---|
| F | through fad7930be including d68c5adc5 and 06a171025 | The protected-polyhedron relative general-position producer and its flat-core consumer are independently accepted in section 100. The producer fixes one actual closed polyhedron Q, builds its own compatible subdivision and gives crossings off Q; the disk consumer still assumes interior support and preserves the original boundary pointwise. Arbitrary boundary charts and full projected-disk normalization remain open. Later F layers 478a65991/0c080405f and the dirty half-space extension require separate frozen-source acceptance. |
| h | throughe85a235df | Produce actual nonstationary locally finite supported modifications with compatible subdivisions, original graph and transported neighborhoods.72fa/c1bd finite solid-torus and generic limit layers are frozen pending replay; a single-increment model does not close arbitrary-stage geometry. |
| E3 | through1dff5b63c | Physical caps and original-target separation are accepted in section92; Q.2a locally finite separating limits are independently accepted in section95. E3 continues Q.2b: two-ended annular exhaustion, adding the center, actual open disk and exact closure. |
| M304 | through3717074e9 | Exact Moise252-to-Moise304 is accepted.6f/823/878/546/e8 original toroidal-shell geometry, Hurewicz and actual Betti2 separator are frozen pending replay. The completee8 delivery triggered the new upstairs Lemma2/L2 round; actual torus recognition remains open. |
| S | throughc0f4df1b1 | Produce original-function extended-arc and relative normal-form geometry in an adequate support region.5b/c011/2544 common coordinates,876 small-frame obstruction,c60 cubic lowering ande24808bce actual descending branch are frozen pending replay. The e248 delivery has continued into actual branch/gamma gluing and relative normal form. General finite cancellation/compact smoothing remain open. |


Section 96 independently accepts F through d68c5adc5, including 06a171025:
the same actual relative perturbation retains quantitative Lipschitz
displacement and preserves old flat boundary crossings while producing new
interior crossings on W union N. Four modules, 25 nonautomatic declarations
(22 in changed leaves and three in an unchanged direct consumer), 20 key
reuses and 12 classified probe declarations pass with zero diagnostics and
only foundational axioms. Seven new public theorems preserve all seven old
public signatures. Three positive geometric assertions and one actual PL
conjugation counterexample are separate from seven helpers and one macro.
Git Lean delta is +871/-217. This is a single-chart layer, not coverage of the
whole transition region or a complete projected NormalSystem normalization.
The later protected-polyhedron author layer is outside this acceptance.

Section 100 independently accepts F through fad7930be. For a fixed actual closed
polyhedron Q it produces the piecewise affine Lipschitz vertex function vanishing
on Q, the Lipschitz displacement extending that perturbation while fixing Q
pointwise, and the small general-position PL homeomorphism off Q; the flat-core
consumer retains crossings on the protected core. Seven modules, 322 nonautomatic
declarations (306 in the four changed leaves and 16 in three unchanged consumers)
and 10 critical reuses pass 13 linters with zero diagnostics and only foundational
axioms. Five public theorems are new and 291 old public signatures are unchanged;
the one authorized signature change removes an unused FiniteDimensional instance
argument. Git Lean delta is +955/-271. The thirteen probes are five positive
geometry assertions, six helpers and two macros, not NormalSystem models. The
batch additionally fingerprints the 288 prerequisites resolved from the shared
read-only build against their recorded declaration ranges; two of them predate
purely additive edits that change no existing statement, and refreshing those two
objects is queued. This is a protected-relative layer, not complete projected-disk
normalization and not a Moise252 endpoint.

The exact sphere endpoint moise304_of_moise252 remains conditional on the
unresolved Moise252. Its independently checked kernel type/body traversals
contain9328 and7200 native constants for the304/tame consumers and omit
Moise303 and broad Moise264. The tame consumer retains its outer-frontier
bicollar. These are the section89 acceptance results, not an unconditional
Loop Theorem,304 or general wild305 proof.

Section92 now independently accepts E3's same actual SurfaceSplitAndCap result:
physical disjoint disk caps, exact old/new carrier equality outside a chosen
ball, a safe path-connected ball frontier, and separation of the original
closed connected targets. Seven modules,34 nonautomatic declarations and17
key reuses pass fresh compile, axiom and13-linter checks. The external audit
has one full unconditional R3 torus/meridian/enclosing-ball/target-pair model,
two lower-dimensional geometry assertions, two conditional consumers and two
helpers. The latter four assertions are not four full three-dimensional models.
All nine old public signatures in the changed modules remain unchanged.
Git Lean delta for the whole c10/c347 integration is+897/-29, including one
root import; ten new public theorems are distinct from the13 old consumer
checks. No source theorem was weakened to make the actual model elaborate.

F's protected-polyhedron relative general position currently solves a
simultaneously flat interior case. An arbitrary PL change of coordinates does
not preserve a small Lipschitz displacement; the explicit counterexample
remains binding. The crucial25.2 gate is actual boundary/transition
normalization of the same disk with original boundary homotopy, normal-subgroup
avoidance and fibers, followed by the genuine cover/elimination argument.
Neither code volume nor the conditional304 endpoint measures Loop Theorem
completion. The route remains plausible; near-term closure is not established.

S's small-frame obstruction formally withdraws arbitrary-prescribed-O
cancellation. Its laterc60 author layer constructs a sufficient longitudinal
R and arbitrary positive transverse width for actual cubic lowering, and the
same original model cancels in a produced larger O'. A protected set inside
O' minus O is not automatically preserved. The next geometric producer must
supply adequate original-function support and relative normal form, not assume
a final cancellation chart or perturbation.

The later M304 shell-homology checkpoint has330 frozen files/52 source
receipt groups. The earlier unresolved-root recognition checkpoint remains
invalid; only recognition-final and sphere-exclusion evidence enter replay.
The h limit theorem consumes genuine increments satisfying its core equations;
the one-increment trivalent model does not produce arbitrary infinitely many
compatible modifications. Both distinctions remain explicit in the queue.

Section95 independently accepts the abstract locally finite separating-limit
producer. All three native declarations and seven key reuses pass13 linters
and foundational-axiom checks. The infinite real-line fixture is moved outside
the generic topology module; its strengthened assertion proves the produced
limit is exactly{0}, while both original targets remain nonempty and every
stage changes. The two public signatures and proof bodies are unchanged.
This supplies Q.2a, not the actual annulus family, open disk or32.1.

Root source reachability is9662 modules with no missing imports or cycles;
this is not full-root compilation. The full-root check remains deferred under
the discretionary compatibility policy. Two private checkers, three total Lean
processes, renewable leases and quiet hourly delivery-boundary coordination
remain unchanged. See integration sections92–95 and the resumed-stage ledger.

### Section32 research and an additional upstream contract gate

[The section32 research](SECTION32_RESEARCH_20260919.md) checks book pages
218,220–232 against current source. Existing local-polyhedral and locally finite
PL-piece APIs can be reused; pseudocells need a separate topological body/rim/
center representation. The infinite construction has two ends, requires local
stabilization away from both, and must prove the final open-disk topology and
exact closure.32.4 is an independent consumer of a given pseudocell.

Moise308 currently assumes the original circle is already a spine of the
intermediate torus. The book needs generation in every admissible intermediate
torus from a spine of the inner torus. Preserve this missing inclusion-map
bridge before consuming31.2/31.4. It was delivered at M304's823 completed boundary for later30.7/30.8 work;
it does not interrupt the new actual30.6 sphere-cut round. Q's old18–27k estimate is historical,
not an execution budget or completion metric. No sixth task was started.

Current source and receipts remain authoritative. Full-root compilation stays
deferred and may restart only for a concrete compatibility or stalled-work
reason. Handoff notices wait for completed deliveries; no new task, mid-round
status request or elapsed-time build trigger is introduced.

### First gate: repair contracts before consuming them

The corrected Moise252/331/351 contracts and actual regular-neighborhood
machinery through h 2086d1064 are independently accepted (handoff section 54).
The produced disk boundary is essential; the small three-dimensional ambient
neighborhood is existential; the locally finite graph and regular neighborhood
are tied to one PL triangulation. The noncompact edge-core model is genuine
but has a disconnected closed-ball ambient. General open-ambient construction
and all three headline proofs remain open. Moise351 retains continuous positive
error functions, a specialization of the book's strongly positive condition.
Do not treat the conditional tetrahedron application as a proof of Moise331.

F now owns an additional correction within its existing cover-production
lane: the fixed normalSystemManifoldComplex formula uses a relative second
derived complex preserving the entire image but requires the ordinary
derived-neighborhood carrier. The independently accepted missing-point theorem
RelativeSimplexNeighborhood (b240763e0) obstructs this equality for a fixed edge
with an ambient coface outside the image. The actual tetrahedron/facet instance
and the current NormalSystem coface consumer both pass kernel/axiom/lint replay.
The coordinator authorized a genuine compatible-neighborhood triangulation
producer and the necessary coherent NormalSystem API correction. Preserve
image faces, the exact carrier, manifold/boundary structure and SDR; do not
add the false neighborhood hypothesis or treat another assumed package as a
producer. The actual compatible triangulation producer c49f666ab + 8728c1b09 is now
independently accepted, including exact carrier, intrinsic boundary and SDR
in a nonempty model. The minimal NormalSystem migration c98ea5828 is now independently accepted
with ff8d66dcf and f2ea6cf4f. All 55 affected consumers, two new producer
modules and three missing old prerequisites were freshly checked. The full
628-declaration audit covers the thirteen author-modified modules and
32 further modules receiving required headers (one also needs an API lint
repair), with fourteen reused entries,
three geometric models and all thirteen applicable environment linters.
Every final check has zero diagnostics and only standard foundational axioms.
The models validate actual neighborhood geometry and an actual anchored
double-cover lift; they are not a full NormalSystem subgroup/avoidance instance.
The exact boundary trace and same-source-complex simplicial lift are actual
producers. The subsequent source-proper cover diagram and geometric cover
reductions through 9bd8d23a7 are now independently accepted, as detailed below.
The original-disk initialization is now independently accepted below; general
singular normalization and the embedded-disk endpoint remain open.

A further source-level gate is now explicit: imageComplex intersect boundary =
loopComplex does not supply the required source preimage boundary equality.
The existing NormalSingularCellData fiber theorem supplies it only after actual
normal data are present; the injective inward-push and NonsingularCell projection
producers cannot be used circularly to initialize a general cover reduction.
The complete delivered boundary/cover layer through F 9bd8d23a7 is now
independently accepted. The source-dependent relative PL collar push fixes the
prescribed source boundary and produces exact source boundary preimage even for
a noninjective map. The actual covering boundary theorem, collapsed simplicial
image subcomplexes, same-source lift and controlled upstairs neighborhoods are
also accepted. For an already source-proper NormalSystem, the construction
produces the complete upstairs NormalSystem and cover diagram. Basepoint and
normal-subgroup transport retain the geometry; actual orientation-cocycle or
nonspherical-boundary covers give strict complexity descent on the same source.
The result does not require a hypothetical cover package as input.

Ten fresh modules, including the existing projected-boundary consumer, and one
combined audit pass with zero diagnostics. The census covers 41 nonautomatic
declarations (35 new, four private), 38 critical reused entries and all thirteen
applicable environment linters. Seven concrete geometric scenarios use eight
theorem declarations; six additional tests are conditional NormalSystem
consumers, and nine local instances are audited separately. They do not provide
an independent nonempty complete NormalSystem instance.

The initial gate is now independently closed through F aef1bbb8e, with
921aa49bd and 27cf1c243. Arbitrary legal cell centers give exact finite
triangulations of noninjective PL maps, preserving both carriers and every map
value. The relative source-boundary push, exact triangulation and actual
image/boundary subcomplexes then construct the complete initial NormalSystem
from the raw PL disk and its original boundary parameterization and subgroup
avoidance. Domain, boundary values, on-loop basepoint, inclusion map and subgroup
comap are retained; source properness and a normal system are not inputs.

Seven freshly checked modules and a complete 145-declaration audit pass with
zero diagnostics, standard foundational axioms and thirteen applicable linters.
Fifty-four declarations are new. The 48 old CellComplex signatures and the three
default definition bodies are unchanged after erasing only generated binder
macro scopes. Three real geometric models include a nonconstant noninjective
folded interval and a constant disk whose pushed interior actually leaves the
neighborhood boundary. Two further consumers are conditional on their stated
raw data; no independent full NormalSystem avoidance instance is claimed.

The preprocessing precedes the initial complexity choice and need not decrease
the original disk complexity. Actual subsequent covers preserve source
properness and strictly decrease complexity. F's actual connected-interior,
spherical-neighborhood, EmbeddedDisk and original-boundary return chain is
now independently accepted through 9658ad75b. The old NonsingularCell source
and return signatures remain unchanged. The sphere producer keeps the actual
domain/map, exact boundary preimage, original loop and subgroup avoidance.

The actual projected double-point covering and free PL partner-involution
layer through 8a00ab535 is independently accepted too. The projected map is
exactly R.projection composed with the upstairs embedded disk map. It retains
source properness and normal-subgroup avoidance; its collision relation and
double sets are polyhedral. Seven modules, all 62 nonautomatic declarations,
42 reused entries and 26 classified external probe declarations pass with
standard axioms, thirteen applicable linters and zero diagnostics. Fifty-five
native declarations are new, including twelve structure-generated members.
Nine concrete geometric theorems are distinct from eleven conditional
NormalSystem/cover consumers; no complete subgroup-avoiding system or cover
instance is claimed. The real rectangle model has a two-dimensional double
image. General crossing regularity, geometric elimination and downstairs
embedding remain open. F continues actual equivariant relative triangulation
within the same descent lane. See integration handoff section 55.

The finite global PL handle-filtration producer is now independently accepted
through S 6690962e1: the actual finite sequence covers the original manifold,
with exact PL attaching maps and relative adjunction homeomorphisms. All 32
nonautomatic declarations, thirty critical reuses, three model declarations and
thirteen applicable linters pass the combined replay. This does not supply the
smooth attaching/atlas compatibility needed by compact smoothing.

The local corner, rounded strip and complete new-cell annulus atlas through
S ada7fd321 are now independently accepted. Nine new modules construct actual
charts and their smooth transitions; 101 nonautomatic declarations, six private
helpers, fifty critical reused entries and three actual geometric tests pass
the combined axiom/lint replay with zero diagnostics. The new-cell neighborhood
contains the entire attaching annulus, including all polygon vertices at all
heights. Its parameter identity g((d x).val.val) = x.val.val ties the atlas to
the original PL attachment. The neighborhood is open in that cell only.
The full triangular-annulus smoothing layer adefc71d0 and preceding local
corner layer 29fc463ce are independently accepted. Fifteen fresh checks and
the combined audit cover 152 native declarations, 52 critical reuse entries,
15 concrete-model declarations and all thirteen applicable linters, with
standard axioms and zero final diagnostics. Of the 27 declarations in the new
leaves, 26 are new and one generalizes and relocates the existing supported
conjugate-family theorem. The old unitInterval consumers now reuse it without
a name collision. These actual isotopies work in the fixed Euclidean atlas,
retaining framing at every height and all three corners. They do not produce
relative smoothing in an arbitrary old atlas or charts across a gluing seam.
S's subsequent bounded-displacement Alexander localization, planar whole-disk
extension, arbitrarily small-support germ linearization, prescribed Jordan
annulus boundary extension and old-atlas local disk smoothing through
c4c935995 are now independently accepted. Thirteen new leaves plus one
unchanged orientation prerequisite were freshly checked. All 92 native
declarations (71 new), 66 critical reuse entries and 51 classified fixture
declarations pass the combined axiom/lint audit with zero diagnostics. The
fixed cusp-shear old-atlas fixture proves the original PL chart is not smooth
and the correcting isotopy is nonidentity. The produced chart belongs to the
original maximal atlas; both transition directions and exact original frames
are retained. This is local zero-handle smoothing, not whole-strip or
cross-seam smoothing. Relative Morse approximation 5beeda255 is subsequently
reported and queued separately; critical-point elimination and a noncritical
parameterization preserving both end collars remain open. S continues its
single relative-strip lane toward the 14:05 UTC checkpoint and 14:19 UTC
deadline. Compact PL smoothing remains unproved. See integration handoff
section 59 and the morning ledger.

h's corrected contracts, same-PL-triangulation exhaustion, real noncompact
three-dimensional edge model and graph dual-cell ballness through 2086d1064
remain independently accepted. The subsequent actual piercing, nested common
neighborhoods, four exact annular traces, real trivalent model and locally
finite numerical scales through c08f3a8d5 are now independently accepted too.
Nine new leaves contain 35 new native declarations and one generalized,
relocated canonical theorem. Its old E3 duplicate and five old calls were
repaired across four consumers. All thirteen modules, 57 native declarations,
90 critical reuse entries, two external geometric probes and thirteen
applicable linters pass with zero final diagnostics and standard axioms.
Nesting is relative to K.space. The ambient neighborhoods are not yet proved standard PL solid tori or mutually
disjoint. Numerical scales do not supply the geometric stability thresholds,
Moise341 approximation or compatible modifications needed for Moise351.
See integration handoff sections 54 and 57.

F's actual spherical EmbeddedDisk, boundary return, projected double-point
cover and free partner-involution layers through 8a00ab535 are independently
accepted. Its active equivariant relative triangulation is a further step;
general desingularization and the loop-theorem headline remain open.

M304 through 4400e3465 is now independently accepted: actual arbitrarily
small annular neighborhoods, original-circle-fixed bicollars and larger disk
pairs from a spanning disk. Twenty-three fresh module checks and one combined
import/model audit cover all 84 declarations, 44 reused entries, twelve actual
geometric models plus four local instances and all thirteen applicable linters.
All final checks have zero diagnostics and standard axioms. The combined audit
caught and repaired the new interval/disk monodromy name collision; the new
interval name ends in _interval, and the established disk API is unchanged.
The E3 refinement consumer is identified but its accepted instantiation remains
pending. The later circle-complement, component-closure, actual capping and
essential separating-circle Betti chain through a10d3b2df is now independently
accepted: nineteen fresh modules, all 49 native nonautomatic declarations
(42 new), 64 reuse entries, 27 probe declarations and thirteen applicable
linters pass with zero diagnostics and standard axioms. Two old consumers
were rechecked with required headers only. The essential Betti theorem starts
from an actual separating compression disk with exact boundary intersection;
its existence is not supplied. The raw caps share that disk and do not give
ambient separation transfer. The concrete cube tests have zero Betti numbers
and do not instantiate strict essential-circle descent. The later annulus
components, supplied-disjoint-cap Betti/compression chain and actual
minimum-Betti separators through ac3673685 are now independently accepted.
All 29 fresh modules, 180 native declarations (40 new), 78 critical reuse
entries, 39 classified probes and thirteen applicable linters pass with zero
diagnostics and standard axioms. The enlarged spanning disks still share the
original disk; the later compression theorem explicitly requires disjoint
caps and separation of their capped union. The general shell minimizer is not
known to have beta zero. M304's essential singular filling b80e381fc and the
actual concrete torus compression/frontier/common-target chain through
1c43107f3 are now independently accepted. A nonspherical closed connected
surface in a simply connected open ambient has an actual essential-boundary
singular PL disk in one finite neighborhood,
with the nontrivial original loop killed by that same disk. Independently,
the concrete triangular-circle solid torus has an essential nonseparating
compressing disk, two actual disjoint caps, an actual capped sphere, and
first Betti number two decreasing to zero. Exact ambient frontier equalities
produce common distinct points separated by both surfaces; external fixtures
also produce common nonempty regions and disjoint three-ball targets. The
full general filling producer is additionally tested on that real torus.
Twenty fresh modules, all 35 native declarations (26 new), 65 critical reuse
entries and thirteen classified fixtures pass with approved axioms, thirteen
linters and zero diagnostics. Native ball-target strengthening 815c38869 is
queued separately. This concrete compression does not settle arbitrary-shell
target preservation, general 26.4/30.3 or Moise304. See handoff section 60.

The held E3 disk-neighborhood chain through 8e0373385 is now independently
accepted: fifteen fresh modules and all 81 native declarations (58 new),
23 critical reuses, two actual geometry models plus their helper declarations,
and all thirteen applicable linters pass with standard axioms and no final
diagnostics. The canonical free-triangle proof is generalized and reused;
the copied chain is removed and both old boundary signatures are preserved.
Actual middle-disk ball pairs and centered prism charts are now producers.
Exact local replacement traces are accepted. The subsequent relative
separation 45c848746 and actual interior WB3 boundary/prism/local-trace bridge
through ff304a1b2 are now independently accepted. Original-ambient separation
is proved in real dimension three, using the actual ball's frontier and
explicit outside equality. Five modules, 25 native declarations (six new),
27 critical reuse entries and three real probes pass the combined audit with
thirteen applicable linters, approved axioms and zero final diagnostics.
The strengthened three-dimensional probe constructs a finite WB3 ambient
around two nondegenerate disks and consumes the full local-trace producer.
It does not instantiate nonempty H,Q for the full separation endpoint.
Physical disjoint caps, a finite replacement surface with manifold structure,
and complete Moise303 remain open. At completed delivery E3 continued exactly
that construction and merged the canonical restriction change. See integration
handoff section 58 and the morning ledger.

### Five tasks: one current lane each

At 2026-09-19 04:24 UTC the owner explicitly authorized a separate 30.4 lane.
M304 starts from cbfe4a73f in its isolated codex/moise-304 worktree; E3 continues
its active 30.3 round without interruption. The private checker limit stays two.

| Task / model | Current round | Delivery gate and next boundary |
| --- | --- | --- |
| h / gpt-5.6-sol max | Contracts and actual neighborhoods accepted; finite disjoint nested neighborhoods and genuinely locally finite disjoint open supports through e8ffd9c5d independently verified. | Localize splitting-disk ballness to finite cofaces without changing the actual disk. Stability, compatible approximation and Moise351 remain open. Checkpoint by14:05 UTC. |
| F / gpt-6-astra max | Actual projected-disk production, equivariant sheets and true-carrier interior local normalization through f5436defe independently accepted. | Later boundary-relative layers through56bd63a74 await replay. Actual boundary half-space collar, overlap-preserving global normalization and four-case elimination remain open. Finish current round safely. |
| E3 / gpt-5.6-sol max | WB3 interior boundary/prism/local traces and original ambient separation through ff304a1b2 independently accepted, with actual 3D WB3 local-trace model. | Produce finite replacement surface/manifold and actual disjoint caps with face equations. Canonical restriction merge assigned at delivery; checkpoint by 14:05 UTC. Full 30.3 remains open. |
| M304 / gpt-6-astra max | Own30.4. Essential filling and actual torus compression through7c38f9f1c independently accepted, including common ball targets and one produced spherical shell. | General prescribed-shell target preservation and zero-Betti descent remain open. Continue only existing concrete compression round; checkpoint by14:05 UTC. |
| S / gpt-6-astra max | Fixed-old-atlas planar smoothing and relative Morse approximation with distinct finite critical values through fa9f81cbf independently accepted. | Relative critical-region cancellation and whole-strip product remain open. Continue only existing level/handle investigation and checkpoint by14:05 UTC. |

F must distinguish the full two-sheeted ambient cover from the smaller regular
neighborhood for the next normal system: restriction need not preserve
two-sheeted surjectivity. The upstairs disk must have the boundary/properness
properties needed by descent. The inward-embedding producer through 3c7d44e19
now constructs proper interior placement from the existing NonsingularCell,
and the actual projection preserves it without extra properness hypotheses. Lemma 2 starts with local injectivity and
two-point fibers. Neither arbitrary NormalSystem data nor the fiber-preserving
DoubleCarrier transport produces them. Generic surface position in dimension
three does not remove triple points. More conditional wrappers do not close
this producer.

The compatible chart along a whole branch remains a separate Lemma 2 gap;
a finite pointwise chart cover does not supply compatible normal directions.
F's source-collapse delivery is diagnostic evidence, not a positive
normalization theorem or a disproof of Moise251.

Existing rounds continue. Handoff at delivery or an urgent stop/restart; do not
send routine status prompts, add a simultaneous lane, or create subagents.
See [FOUR_LANE_WORKFLOW.md](FOUR_LANE_WORKFLOW.md).

Source review rejected h's initial 585cc71a0 contract repair because it excluded
branch vertices in 33.1 and used raw stars without derived/global compatibility
in 35.1. Later deliveries correct the graph input and strengthen the ambient PL
exhaustion, with actual nonconstant examples. They remain queued for independent
statement, consumer and axiom replay; the older rejected statement is not the
current proposed contract. No general Moise331 or Moise351 theorem is accepted.

The independently accepted shared closed-cover lemma has one public home in
Connected/ClosedCover. F withdrew its duplicate ClosedAttachment publication;
M304 supplied the isolated dependency before continuing its own surface work.
This was an urgent source-ownership correction, not another lane or a status
prompt. F can reuse isPreconnected_left_of_isClosed_union for sphere geometry.
Its broader separation helper can use the existing Mathlib closed-cover API;
no duplicate public theorem has been added.

### Subsequent mathematical gates

The owner added one independent M304 lane on 2026-09-19 UTC, leaving E3
on actual 30.3 geometry and all other existing lanes unchanged. M304's
first independently accepted layer (f0f7bd699) constructs finite connected
orientable two-sided
polyhedral surfaces separating arbitrary disjoint compact/closed connected
sets, with arbitrary neighborhood control. Five new declarations, ten
critical reuse entries, one nonempty geometric model and 13 applicable
environment linters pass; only standard axioms occur. A second independently accepted layer (0289bdaf4)
constructs the radial annulus homeomorphism, proves the exact shell frontier
and simple connectivity of its interior, and constructs the initial
separating surface inside that interior. Its 24 declarations, ten reused
entries, three geometric models and 13 applicable linters pass. Compression
and the PL-sphere endpoint remain open. A third source-checked layer captures
actual nullhomotopies in finite polyhedral neighborhoods and constructs a
nontrivial inclusion-kernel element for each non-spherical connected closed
surface inside a simply connected open set. It supplies the finite ambient
inputs to 26.4 without assuming 26.4 or a compressing disk. A fourth checked
layer constructs the cyclic two-disk neighborhood of a surface circle,
prescribed disjoint boundary-arc maps, rectangle parametrizations and the
actual interval-fiber cylindrical diagram of that neighborhood. All 28
declarations in seven mathematical modules, ten reused producers, three
nondegenerate models and 13 applicable linters pass; all five direct old
consumers compile. A fifth checked layer constructs the Mobius model of
the reversing interval end map, excludes it inside an orientable surface,
and untwists the remaining diagram to produce an actual PL annulus. It also
constructs an annular neighborhood of any PL circle in an orientable finite
surface inside every prescribed open neighborhood. Its 12 declarations,
12 reused entries, three actual models and 13 applicable linters pass.
A sixth checked layer fixes the original circle pointwise as the middle
circle of an arbitrarily small PL bicollar in the surface interior. It
proves circle-map extension across two-spheres and preservation of interior
neighborhoods under PL embeddings, then transports a spherical bicollar
through the constructed annular neighborhood. All seven new declarations,
12 reused producers, three geometric models and 13 applicable linters pass.
A seventh checked layer adjoins the two halves of the circle bicollar to
an actual spanning disk. It produces two actual PL disks meeting exactly
in the original disk, each containing it away from its intrinsic boundary.
Their union is a relative neighborhood of the disk in the surface-disk
union, with prescribed neighborhood control on the added parts. All five
new declarations, ten reused entries, three models and 13 linters pass.
Instantiation into E3's later disk-pair subdivision endpoint awaits accepted
downstream artifacts. An eighth checked layer extracts an actual disk
parametrization from a sphere capped by a disk with the exact boundary
intersection. It constructs nullhomotopies through PL balls and along
cylinders ending in them, including transport from the capped sphere's
complement. Six declarations, ten reused entries, three geometric models
and 13 applicable linters pass. The actual capped components and their
maps back to the source surface still have to be constructed before this
can exclude spherical components in compression. Four checked Betti
corollaries now consume actual `SurfaceSplitAndCap` data: a connected
orientable result has first Betti number exactly two below the source;
for a disjoint union of two connected orientable non-spheres each first
Betti number is strictly below the source. Their full axiom and 13-linter
audit passes. A further checked layer constructs the at-most-two component
description of a surface minus a PL circle. In the separating case the
actual two component closures cover the surface and meet exactly in the
circle. This uses the produced bicollar, not a supplied decomposition.
Eight declarations, eight reused entries, three concrete models and all
13 applicable linters pass. Actual local disk pairs now prove that the
separating-circle component closures are finite connected orientable
surfaces with boundary. For a closed source both boundaries are precisely
the original circle; the version with boundary also identifies the inherited
old-boundary parts. Seven new declarations and one retained declaration,
ten reused entries, three concrete models and 13 linters pass; two old
consumers compile unchanged. General entire-boundary gluing is now checked
in every dimension: two balls give a sphere, and two manifolds with boundary
give a closed manifold on their actual union, even with initially unrelated
triangulations. Eight new declarations, ten reused entries, three geometric
models and 13 linters pass. Actual separating-circle component closures are
now capped by the given spanning disk to produce two connected closed
surfaces with Euler sum equal to the source Euler characteristic plus two.
In ambient dimension three, essentiality excludes both caps from being
spheres and gives an exact Betti sum and strict descent for each. Six new
declarations, eleven reused entries, three models and 13 linters pass.
The raw caps share the given disk; nonseparating compression and preservation
of the original separation are still open. Full nonorientable 28.19
and the spherical-shell
endpoint remain open. Exact evidence
and the source route are in HANDOFF_CODEX_M304.md. This explicitly authorized
addition supersedes the older four-lane count, without authorizing subagents.

1. Accept corrected contracts and a real cover/projection construction; complete
   Lemmas 1 and 2 and the covering induction before claiming 25.1/25.2.
   Boundary non-nullhomotopy/subgroup avoidance must survive actual operations.
2. Prove 26.4 and 28.19; E3 completes actual 30.3 geometry and M304 owns 30.4. The accepted
   Moise304-to-Moise305Tame arrow has a bicollar hypothesis; general wild-cell
   Alexander duality is not an extra prerequisite of that tame arrow.
3. Continue 30.6 -> 30.7, 30.8 and sections 31--35 with the open producers
   listed in the detailed Phase 3 table. There is no 30.7 -> 30.6 edge.
4. S is working on compact PL smoothing as a separate phase. The actual
   finite triangulation, handle/collar, sphere-isotopy and interior-atlas
   inputs have been audited. Prescribed sphere reparametrizations now extend
   to actual cell-adjunction homeomorphisms with exact lower/cell formulas.
   Actual vertex zero handles and edge one-handle attachments, including
   intrinsic boundary traces and successor-subcomplex homeomorphisms, are now
   constructed. Actual triangle two-handles now have their PL annulus pair,
   framing and lower-fixing adjunction for finite closed K. Maximal-cell sphere
   pairs and actual tetrahedral three-handles are also constructed. The actual global
   finite sequence has been delivered and awaits independent acceptance. Smooth
   attaching/framing, corner rounding and classification of terminal two-sphere
   boundaries remain open.
   The eventual compact assembly does not prove unrestricted PLSmoothing 3.
5. Only after both inputs are produced, assemble a smooth structure on the
   same carrier and topology and audit its transitive axioms.

### Acceptance queue and full-root hold

E3 b195204ed and b5e36cfe5 are independently accepted: two modules, 35
nonautomatic declarations and 12 key reused declarations pass the axiom/lint
audit. h's corrected contract/neighborhood layer through 2086d1064 is independently accepted. F through 51b4ee8ad is
independently accepted: nine modules, 92 nonautomatic declarations, 15 critical
reuse entries, two nonempty models and 13 clean environment linters. The
source-collapse result is conditional on a given NormalSystem. Complete cover
diagram production remains open; conditional strict descent and finite-cover
realization are accepted as recorded below. F through 3c7d44e19 is
subsequently accepted: five modules, 23 declarations (18 new), 13 critical
reuse entries, four concrete models and 13 clean linters. S cap comparison 4627710d3 and actual graph handles 3c08c2aba are
independently accepted: seven modules, 27 declarations, 34 critical reused
names and two concrete geometric scenarios.
S's actual disk-times-circle product and
finite native 24.11/24.12 through 434d5352c are independently accepted: ten
modules, 41 declarations, 33 critical reused declarations, 13 clean linters
and a nonempty endpoint instance. Preserve S's
extraction of IsTopologicalSolidTorus when integrating h's separate MoiseChain
repairs.

The owner stopped the independent full-source build at 2026-09-19 02:00 UTC.
Completed artifacts are retained and the run is incomplete. After the account
switch, the owner authorized a discretionary rebuild when integration
compatibility requires it, or when all lanes are persistently blocked and no
more productive proof work remains. Eight hours was an example, not a timer.
Proof work and focused checks take priority. A restart must record its reason
and keep the existing one-root-worker/two-private-checker resource policy.

The six-import root coverage repair is applied: Approximation,
ApproximationManifold, ChartGluing, Endgame, Smoothing and PLSchoenflies.
Static traversal reaches all six and 9363 project modules including the root,
with no missing project source. This is import coverage, not a successful root compilation.
The first five were unreachable; PLSchoenflies was reachable transitively but
lacked direct flat-root registration. Seven relevant leaves have fresh focused
checks covering 26 nonautomatic declarations, standard axioms and all 13
applicable environment linters; this does not establish full-source success.

Next integration work is to review and replay pending deliveries and check
changed modules, dependents and endpoint axioms. Root coverage is repaired.
The root build is currently stopped. When the discretionary restart criteria
are met, reuse retained artifacts and check the expanded import graph before
treating a root success as endpoint coverage.
Current AGENTS allows required copyright/authors headers and module docstrings;
inline comments and declaration docstrings remain disallowed.

### Locally finite support-separation gate (2026-09-19 UTC)

The finite incident family now has pairwise-disjoint outer and inner actual
piercing neighborhoods. For every locally finite PL ambient, all splitting
disks have finite faces and form a locally finite closed disjoint family;
locally finite disjoint open supports are constructed in any prescribed
containing open set. Both a compact trivalent three-sphere model and a
noncompact R3 model with nonempty disks and supports are independently checked.
Through e8ffd9c5d, four modules, all71 native declarations,26 reused entries
and two actual probes pass the axiom/lint gate. The same-disk local PL-ball
bridge, solid-torus classification, geometric stability and Moise351 remain
open. h continues that same lane until the final checkpoint; see section61.

### Relative Morse neighborhood gate (2026-09-19 UTC)

Relative continuous-to-smooth Morse approximation and distinct critical values
through S fa9f81cbf are independently accepted. The original atlas and regular
closed collars stay fixed, and the whole compact core has an open neighborhood
with compact closure inside a prescribed frame, finite nondegenerate critical
points and distinct critical values. Proper input remains proper. The supported
critical-value change preserves the entire ambient critical set, even when
infinite. Actual nonsmooth cusp-shear and infinite-critical-set cosine models
pass. This does not remove the critical points or supply the full strip product;
relative cancellation and seam gluing remain the next smoothing gate. See
handoff section62 for13 native declarations,45 reused entries and25 classified
model declarations, all with approved axioms and thirteen applicable linters.

### Concrete shell-compression gate (2026-09-19 UTC)

The actual torus compression through M3047c38f9f1c now has common disjoint
three-ball targets and an actual produced spherical shell. Both surfaces,
the whole compression three-ball and the same essential spanning disk lie
inside that shell, and both surfaces separate its real boundary spheres.
For this shell the existing minimum-Betti separator is independently proved
a PL sphere by comparison with the actual capped sphere. General prescribed-
shell target preservation and zero-Betti descent remain open; this specific
example does not close Moise304. Six fresh modules,31 native declarations,
57 reused entries and nine actual certificates pass; see handoff section63.

### Equivariant double-sheet and interior-normalization gate (2026-09-19 UTC)

F through f5436defe is independently accepted: relative equivariant finite
triangulations of actual double-point involutions, finite saturated polyhedral
sheet neighborhoods, and the projected disk in the actual double with its
exact boundary and fibers. At interior double points a small single-chart
modification preserves the carrier, fixes the boundary and produces local
crossings. Five leaves and nine native declarations pass. Four actual model
theorems are distinct from five conditional NormalSystem consumers. Global
overlap-preserving normalization, boundary chart production and four-case
elimination remain open; later source through56bd63a74 is queued separately.
See handoff section64. Moving to the double alone leaves fibers unchanged.

### Actual meridian gate (2026-09-19 UTC)

M304 through 6fa7957c9 is independently accepted: the actual embedded meridian
is essential in the same torus boundary and bounds its actual interior disk.
The boundary inclusion has a nontrivial fundamental-group kernel. General
loop-theorem production and prescribed-shell Moise304 remain open. Two new
leaves, two native declarations and three probes pass; see handoff section 65.

### Planar cancellation gate (2026-09-19 UTC)

S through f081c3b24 is independently accepted: an actual compactly supported
critical-point-free replacement of every positive-parameter planar cubic pair,
with an exact two-critical-point/nonidentical/exterior-fixed a=1 model. The
support is not prescribed. General surface pairing and geometric reduction,
finite iteration and strip assembly remain open. S stopped its round cleanly;
see handoff section 66.

### Closed-interval meridian gate (2026-09-19 UTC)

M304 through e83d02f94 is independently accepted: every closed-interval
height of an actual finite untwisted disk cylinder supplies its proper
essential meridian, including both glued ends. The connected-complement API
now includes endpoints; all six affected module suites pass together. General
prescribed-shell cylinder production and Moise304 remain open. See section 67.

### Locally finite disk-ball gate (2026-09-19 UTC)

h through bbd11df3b is independently accepted: ballness of the original
splitting disk now follows from local finiteness and the actual combinatorial
manifold, without global finite faces or assumed ballness. The noncompact
example is an explicit disconnected family of three-spheres in R4. All 85
declarations in three modules pass; nine are new. h stopped cleanly. Stability,
compatible modifications and Moise351 remain open; see handoff section 68.

## 1. 目标与接口

- 数学目标：Hausdorff、第二可数的紧致无边界拓扑三维流形 `M`，在同一 carrier、同一拓扑上存在光滑结构。
  只要存在性；不要求唯一性、Hauptvermutung、完整 Pachner 定理，也不重做 Ricci flow。
- 书中消费者接口（`master05a.tex` `thm:moise-smoothability`，节点 `PC-DI-SMOOTHABILITY` / `FND-SMOOTHABILITY`）：

  ```lean
  theorem ... [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [CompactSpace M] :
      ∃ s : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M, letI := s; IsManifold (𝓡 3) ∞ M
  ```

  `TopologicalSpace M` 固定不变，只对 `ChartedSpace` 存在量化。唯一消费者是拓扑版 Poincaré 装配
  (`thm:pc-topological-assembly`)，它只需要紧致情形。截至 2026-09-11 库中还没有该接口的 Lean 消费者声明。
- 初始假设只允许拓扑流形条件（`ChartedSpace ℝ³ M` 只提供拓扑图卡；不得要求给定图卡已是 PL/光滑）。

## 2. 基线与工作区（2026-09-11）

- 共享检出 `E:\differential-geometry-dev`，按负责人指示 `main` 已重置到 `origin/main@806b541e9`
  （旧本地 `main@9cdb3d0cc` 保存在分支 `backup/main-local-20260911`，204 个未跟踪文件另存
  `E:\dg-local-backup-20260911` 并原地保留）。本任务分支：`codex/moise-smoothing`（自 806b541e9）。
- 工具链 Lean/Mathlib `v4.33.1`。完整 `lake build DifferentialGeometry` 在该检出运行
  （`LEAN_NUM_THREADS=2`，日志 `.lake/build-main.log`，内存看门狗）；孤儿构件已清理，
  缺失构件以只读方式从 `D:\differential-geometry-candidate` 的暂停构建播种。
- 当前 `AGENTS.md`（Codex 版）是工作流权威：非 vendored Lean 源零注释、零 docstring；
  按模块名构建；新叶子登记到 `DifferentialGeometry.lean`；重要端点做 `#print axioms`。

## 3. 复用清单（源码审计快照，未重新构建外部项目）

| 来源 / 提交 | 实际声明 | 假设 | 结论 | 额外公理 / sorry | 维数 | 适配成本 / 结论 |
|---|---|---|---|---|---|---|
| Mathlib v4.33.1 | `ChartedSpace`, `StructureGroupoid`, `Pregroupoid`, `Pregroupoid.groupoid`, `HasGroupoid`, `ClosedUnderRestriction`, `Opens.instChartedSpace/instHasGroupoid`, `Homeomorph.chartedSpace`, `StructureGroupoid.LocalInvariantProp` | 任意模型空间 | 图卡/群胚框架 | 无 | 任意 | 直接使用：PL 结构 = `HasGroupoid M (plGroupoid n)` |
| Mathlib v4.33.1 | `Geometry.SimplicialComplex 𝕜 E`, `PreAbstractSimplicialComplex`, `AbstractSimplicialComplex` | 向量空间中的几何复形 | 面、`space`、交面条件 | 无 | 任意 | 后续三角剖分层使用；不另造平行体系 |
| Mathlib v4.33.1 | `metrizableSpace_of_t3_secondCountable`, `ChartedSpace.secondCountable_of_sigmaCompact`, `ChartedSpace.locallyCompactSpace`, `Metric.infDist`/`continuous_infDist_pt`, `IsClosed.notMem_iff_infDist_pos`, `Continuous.homeoOfEquivCompactToT2`, `AffineMap.continuous_of_finiteDimensional` | — | 点集/度量工具 | 无 | — | Phase 1 直接使用 |
| 本库 `Topology/Manifold/HomeomorphAtlas.lean` | `exists_smoothAtlas_of_homeomorph (h : M ≃ₜ N)` | `M` 无边界光滑流形 | `∃ C : ChartedSpace E N, IsManifold 𝓘(ℝ,E) ∞ N ∧ ∃ d : Diffeomorph ..., d = h` | 标准 | 任意 | 路线第 3 步“沿同胚运输光滑结构”已有生产者 |
| 本库 `Topology/Manifold/Homeomorph/Transport.lean` | `pullbackChartedSpace`, `instHasGroupoidPullback (h : X ≃ₜ M) (G)` | `HasGroupoid M G` | `HasGroupoid X G` | 标准 | 任意 | 任意群胚结构沿同胚拉回；PL 结构运输可直接复用 |
| 本库 `Topology/Manifold/SmoothOpenCover.lean`, `Atlas.lean` | `exists_smoothAtlas_of_openCover`, `isManifold_of_contMDiffOn` | 光滑相容开覆盖 | `ChartedSpace` + `IsManifold` | 标准 | 任意 | 光滑侧装配模板 |
| 本库 `Topology/SimplicialComplex/*` | `geometricRealizationHomeomorphism`（有限 `Geometry.SimplicialComplex ℝ E`）、`geometricLink`、`faceEulerChar`、`GeometricManifoldLinks` 等 | 有限几何复形 | 实现同胚、link、Euler 数 | 未审计 | 任意 | 三角剖分层可复用；不重造 |
| 本库 `Topology/Homology/*`, `Topology/SphereSeparation/*` | 局部同调、Jordan–Brouwer、Alexander 对偶、`isOpen_range_of_isImmersion`（光滑） | — | — | 未审计 | — | 拓扑不变域定理**尚无原生声明**；若后续需要可由此推出 |
| 本库 `External/Schoenflies/`（alonamaloh/schoenflies-lean@05a43d2） | 平面 Jordan–Schoenflies | 平面 | 平面 | 见其 README | 2 | 仅平面；对三维 Moise 只在 2D 模型章节有用 |
| 本库 `Topology/ThreeManifold/SmoothSchoenflies.lean`（分支 `origin/codex/smooth-schoenflies-three`，有负责人） | `smooth_schoenflies_three (e : S² → ℝ³) (he : IsSmoothEmbedding ...) : ∃ Φ : ℝ³ ≃ₘ ℝ³, Φ '' S² = range e` | **光滑**嵌入 | 光滑 Schoenflies | 直接 `sorry` | 3 | 与 Moise 需要的 **PL** Schoenflies（Alexander，Moise GTM47 §17：PL 2-球面界定 PL 3-胞腔）是不同定理；互不推出（需 PL/光滑比较）。不重复其证明；本路线不依赖它。书中 `FND-SCHOENFLIES` 卡片允许该负责人反过来经 PL 链得到光滑版 |
| mccorvie/classification-of-surfaces@e3c7230 (Lean 4.32.0, Apache-2.0) | `moise_triangulation : Nonempty (GeometricTriangulation S)`，`moise_triangulation_explicit`；链 `Moise.moise_triangulation_of_boundaries`→`ChartInduction.lean`(5815 行) | `[T2Space S] [ConnectedSpace S] [CompactSpace S] [ChartedSpace (EuclideanHalfSpace 2) S] [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]` | 有限顶点集、三顶点面族、重心实现 `GeometricRealization V F ≃ₜ S` | 源码无 `sorry`（`JordanCurve/Main.lean` 的匹配只是 docstring 文字）；未本机审计公理 | 2 | 其 PL 机器类型为平面专用（`Plane`, `TriangleMesh`, `PlaneComplex`, `FinitePLHomeomorphOn`, 直线公共细分, `PolygonalSchoenflies`）；维数无关部分只有重心实现 `GeometricRealization V F ⊆ (V → ℝ)` 与重标号，且与本库 `Geometry.SimplicialComplex` 实现重叠。**不能改 2 为 3**；其 2D 图卡归纳是 Moise GTM47 §8 的实现，对应本路线的“拼接桥”在 2D 的实例。其 `Topology/InvarianceOfDomain.lean`（813 行，`invariance_of_domain_open_map`，维数无关的解析证明）是 Phase 3 的单文件移植候选；其 `classification_of_surfaces`（拓扑版，依赖 142k 行）不整体移植 |
| not-gary/pachner@df9ad40 (Lean 4.21.0-rc3, Apache-2.0) | `AbstractSimplicialComplex E`（faces : Set (Finset E)），`StellarSubdivision`, `StellarMove/StellarEquiv`, link/star/join/cone，`stellarSubdivision_simplicialIso` 等 | 抽象复形 | 星形细分与 link/join 关系 | 0 `sorry`（14.6k 行） | 任意 | 与 Mathlib `PreAbstractSimplicialComplex` 同构；组合流形定义/细分层（Phase ≥3）可移植；**无**流形三角剖分存在定理，完整 Pachner 定理未完成 |
| deancureton/sphere-six-complex@9bf61f6 (Lean 4.34.0-rc1) | `SmoothManifold.finiteCWModel`, `ManifoldWithCorners.relativeCWComplex` | 已有 C¹ 光滑结构 | 有限 CW 同伦模型 | **`public axiom`** | 任意 | 不可作已证存在定理移植；与目标方向相反（假设光滑） |
| TauCeti Roadmap | — | — | — | — | — | 路线图，非证明 |
| 数学来源 | Moise, *Geometric Topology in Dimensions 2 and 3* (GTM 47)，本机 `D:\数学文档\拓扑\...Moise...pdf`：§5–8（2D 模型；定理 8.4 开集逼近形式）、§17 PL Schoenflies、§23 三角剖分 3-流形、§24–27 覆盖/环定理/Dehn、§30–34 多面体插值与 PLH 逼近、§35 定理 35.2/35.3、§36 定理 36.1；Bing 1959；Shalen 1984；用户 `Moise_Theorem.zip` 的 `main04.tex`（仅章节合同，无证明） | | | | | 本路线以 Moise §35–36（Shalen 式）为 A 的经典来源 |

## 4. 证明路线

记 `ℝⁿ := EuclideanSpace ℝ (Fin n)`。

1. **R1（TOP → PL）**：紧致拓扑 `n`-流形 `X` 的有限图卡覆盖 `U₁,…,U_k`，每个 `Uᵢ` 带由图卡运输的欧氏 PL 结构；
   按 Moise §8/§35 的图卡归纳逐个并入：设 `U` 已有 PL 图册 `A`，`V` 有 `B`，`O = U ∩ V`。
   对 `id_O : (O, A|O) → (O, B|O)` 用**逼近定理 A** 得 PL 同胚 `f : O → O` 且
   `dist (f x) x < ½·infDist x Oᶜ`；把 `f` 用恒同延拓成
   `F : X ≃ₜ X`（边界处连续性由该控制给出，双射由 `f(O) = O` 给出，不需要不变域定理），
   `F(U) = U, F(V) = V`；把 `A` 沿 `F` 运输后与 `B` 在 `O` 上逐图卡 PL 相容，取并得 `U ∪ V` 的 PL 图册。
   有限归纳后得 `∃ C : ChartedSpace ℝⁿ X, HasGroupoid X (plGroupoid n)`。除 A 外维数无关。
2. **R2（PL → DIFF）**：`n = 3` 时每个 PL 3-流形有兼容光滑结构（Moise/Whitehead/Munkres；
   障碍群 `Γ₁ = Γ₂ = 0`）。作为**光滑化接口 B** 显式陈述：同一 carrier、同一拓扑上由 `HasGroupoid X (plGroupoid 3)`
   得 `∃ C' : ChartedSpace ℝ³ X, IsManifold (𝓡 3) ∞ X`。
3. **R3（接入原生接口）**：B 直接给出书中接口形式；若 B 以“光滑模型 + 同胚”形式证明，则用
   `exists_smoothAtlas_of_homeomorph` 或 `pullbackChartedSpace` 运输。

### 4.1 PL 的原生表示

- `IsHPolytope C`：有限个闭仿射半空间之交且有界（紧）；对仿射映射原像、仿射等价像、有限交封闭；
  有限维空间中每点在任一开集内有 H-多面体邻域（坐标立方体）。
- `IsPiecewiseAffineWithinAt f s x`：存在有限个 H-多面体 `Cᵢ ⊆ s`，`⋃ Cᵢ ∈ 𝓝[s] x`，`f` 在每个 `Cᵢ` 上与一个仿射映射相等；
  `IsPiecewiseAffineOn f s := ∀ x ∈ s, IsPiecewiseAffineWithinAt f s x`。用 `𝓝[s] x` 而非 `𝓝 x`，
  使同一定义既适用于开集（此时二者相同）也适用于多面体（Rourke–Sanderson / Moise 意义下的多面体上 PL 映射）。
  与“对某个三角剖分逐单形仿射”等价（胞腔复形的单纯细分定理），需要时另证。
  已证性质：恒同、限制（`inter_of_mem_nhds`/`of_inter_of_mem_nhds`）、局部性、congr、复合
  （用 `Cᵢ ∩ Aᵢ⁻¹(Dⱼ)`，不需公共细分）、集合内连续、同胚的逆（先舍去内部为空的多面体——它们无处稠密——再用仿射等价像）。
- `piecewiseAffineProperty n m` 是 `plGroupoid n`/`plGroupoid m` 的 `StructureGroupoid.LocalInvariantProp`
  （`Manifold.lean`），由此 PL 流形之间的映射 `IsPLWithinAt/IsPLAt/IsPLOn/IsPL n m f` 通过 Mathlib 的
  `ChartedSpace.LiftProp*` 定义，并自动得到图卡无关性（`isPLAt_iff_of_mem_maximalAtlas`）、恒同与图卡为 PL。
- 多面体层（`Polyhedron.lean`）：`IsPLHomeomorphOn f P Q`（`BijOn` + 双向逐块仿射）、`IsPLBall n`/`IsPLSphere n`
  （与标准单形 / 其边界 PL 同胚）、`IsCombinatorialManifold n K`（Moise 定义：顶点 link 是 PL `(n-1)`-球面；
  `n = 0` 时 link 为空）、`PLTriangulation n X`（有限几何复形 + 与 `X` 的 PL 同胚，逐图卡逐块仿射）。
- `plPregroupoid n : Pregroupoid ℝⁿ`，`plGroupoid n := (plPregroupoid n).groupoid`，`ClosedUnderRestriction`。
  PL 流形 = `[ChartedSpace ℝⁿ M] [HasGroupoid M (plGroupoid n)]`；流形间 PL 映射逐图卡定义。
- 开子集上的部分图册 `AtlasOn G U`（`G` 任意结构群胚，`U : Set X`）：图卡为 `OpenPartialHomeomorph X ℝⁿ`，
  source ⊆ U 且覆盖 `U`，两两转移在 `G` 中。运算：限制、沿 `X ≃ₜ X` 运输、相容并、`AtlasOn G univ → ChartedSpace + HasGroupoid`。

### 4.2 显式上游接口（无负责人，本任务自有；下游结果一律报告为条件性）

- **A `PLApproximation n : Prop`**（Moise GTM47 定理 36.1 / Shalen；书中 `thm:boundaryless-approx-main04` 无相对项版本）：
  对 T2 第二可数空间 `X₁`、带度量的第二可数空间 `X₂`、开集 `O₁ O₂`、其上的 PL 图册 `A B`、同胚 `h : O₁ → O₂`
  （`OpenPartialHomeomorph X₁ X₂`，source/target 恰为 `O₁ O₂`）以及在 `O₁` 上连续且为正的控制函数 `φ : X₁ → ℝ`，
  存在同胚 `f : O₁ → O₂`，`∀ x ∈ O₁, dist (f x) (h x) < φ x`，且对 `A` 的每个图卡 `e`、`B` 的每个图卡 `e'`，
  `e.symm ≫ₕ f ≫ₕ e' ∈ plGroupoid n`（即 `f` 及其逆逐图卡分段仿射，也就是 Moise 的 PLH）。
  这正是 Moise 36.1 的 φ-逼近形式（Moise 的“强正函数”被连续正函数取代，二者在此等价：连续正函数强正；
  强正函数在局部紧可分空间上有连续正下界）。目标空间的度量任意，与 Moise 一致。该命题在 `n ≤ 3` 为真
  （`n = 2` 即 Moise 定理 8.4，`n = 3` 即定理 36.1），`n ≥ 4` 为假；因此条件定理不隐藏目标。
  拼接桥只用 `X₁ = X₂ = X`、`h = id_O`、`φ x = ½·infDist x Oᶜ` 的特例。
  流形语言的同一陈述 **A′ `PLApproximationManifold n`**（`Manifold.lean`：PL `n`-流形 `M₁ M₂`、同胚 `h`、
  连续正 `φ`，存在同胚 `f` 满足 `IsPL n n f` 并 φ-逼近 `h`；逆映射自动 PL：`isPL_symm_of_homeomorph`）
  是未来经典证明的自然目标；
  `A′ → A` 的归约已证：`plApproximation_of_plApproximationManifold`（`ApproximationManifold.lean`；
  `AtlasOn.subtypeChartedSpace` 把开集上的图册变成子类型上的图卡空间并继承群胚，
  `OpenPartialHomeomorph` 与子类型同胚互换，再用 `isPLAt_iff_of_mem_maximalAtlas` 转回逐图卡群胚条件）。
  因此未来只需在流形语言中证明 A′（`n = 3`）。
- **B `PLSmoothing n : Prop`**：同一 carrier/拓扑上 `HasGroupoid X (plGroupoid n) → ∃ C', IsManifold (𝓡 n) ∞ X`。
  `n ≤ 7` 为真（`n = 3` 经典），`n = 8` 为假。更弱的 **B′ `PLSmoothingModel n`**（只要求存在与 `X` 同胚的光滑模型）
  已证蕴含 B（`plSmoothing_of_plSmoothingModel`，用本库 `pullbackChartedSpace`），所以 Phase 2 只需证 B′。
- **T1 `CombinatorialManifoldPLStructure n`**：有限组合 `n`-流形 `K` 的实现 `K.space` 有 PL 图册，且图卡与 `K` 的线性结构
  逐块仿射相容。**T2 `PLManifoldTriangulation n`**：紧致 PL `n`-流形有 `PLTriangulation`，其复形是组合流形。
  两者是 A、B 的经典证明与图册模型之间的桥（Moise §7 定理 5–6、§23；Rourke–Sanderson 第 3 章）。
- 两者都以 `Prop` 定义 + 显式假设出现在定理签名中，**不引入 `sorry`/`axiom`**；条件定理不使用经典定理名
  （NAMING.md §3：不得靠命题假设获得经典名）。

## 5. 阶段

### Phase 1（进行中，2026-09-11 起）：PL 基础 + 图卡拼接桥 + 条件性端点

文件（`Topology/PiecewiseLinear/`；根登记缺口及待应用修复见本文件当前计划）：

1. `Polytope.lean` — `IsHPolytope` 及其封闭性、立方体邻域。
2. `PiecewiseAffine.lean` — `IsPiecewiseAffineOn`：id、congr、限制、局部性、复合、连续性、同胚之逆。
3. `Groupoid.lean` — `plPregroupoid`, `plGroupoid`, `ClosedUnderRestriction`，模型空间 `HasGroupoid`。
4. `Topology/Manifold/PartialAtlas.lean` — `AtlasOn G U` 与运算（群胚通用）。
5. `Approximation.lean` — `PLApproximation n` 的定义。
6. `ChartGluing.lean` — 两集合拼接桥（度量控制 → 全局同胚 `F` → 运输 + 并），有限图卡归纳：
   `PLApproximation n → ∀ 紧致 T2 [ChartedSpace ℝⁿ X], ∃ C, HasGroupoid X (plGroupoid n)`。
7. `Smoothing.lean` — `PLSmoothing n` 定义；端点
   `PLApproximation n → PLSmoothing n → ∃ C : ChartedSpace ℝⁿ X, IsManifold (𝓡 n) ∞ X`，
   并给出 `n = 3` 的书中接口形式。

8. `Manifold.lean` — PL 群胚的局部不变性质与 PL 流形间映射 `IsPL* n m`。
9. `Polyhedron.lean` — PL 同胚、PL 球/球面、组合流形、`PLTriangulation`，以及桥接口 T1、T2 的陈述。
10. `ApproximationManifold.lean` — 开集图册的子类型图卡空间；`plApproximation_of_plApproximationManifold`。

验收：每个模块按模块名构建通过、零警告；端点 `#print axioms` 只含标准公理；条件性由签名显式表达。
已证生产者：1–4、6 的桥与归纳、7 的装配。条件性消费者：6、7 的端点（依赖 A、B）。

### Phase 2（独立开放输入，2026-09-19 核实）：紧致 PL 三维流形的光滑化

优先生产紧致情形的 B′，并给当前紧致最终消费者单独的装配定理；这不等于生产现有不要求紧致的 `PLSmoothingModel 3`。

候选路线：紧致 PL 3-流形的有限柄分解（来自三角剖分的二次导出细分）+ 本库光滑柄粘接
（`Topology/Handle/*`, `Topology/Morse/Attachment/*`）；0/1-柄直接光滑，2-柄需光滑曲面中 PL 圆周的光滑化与框架，
3-柄需“同胚于 S² 的光滑闭曲面微分同胚于 S²”（`Γ₂ = 0` 型 2D 输入）。这些 2D 输入是 B 的真实数学成本，须先审计
本库 `Topology/Manifold/Sphere*`、`ClosedBall`、`Morse` 现有生产者。B 也需要 Phase 3 的“PL 图册 ⇔ 组合三角剖分”桥。

**S 的首层已闭合（2026-09-19，独立整合验收通过）：** `Homeomorph/SphereExtension.lean` 的
`sphereRadialHomeomorph`/`closedBallHomeomorphExtension` 从任意实赋范空间单位球面间的同胚生产实际保范数的径向同胚；
`Attachment/Homeomorph.lean` 的 `adjunctionHomeomorph` 证明两个附着交换方块诱导实际商空间同胚；
`Attachment/CellExtension.lean` 的 `cellAdjunctionHomeomorph` 据此处理指定球面边界重参数化，保留底空间和胞腔的逐点公式。
三模块 19 个非自动声明（含 3 private）、14 个关键复用条目、每模块 13 环境 linter 全过，检查 exit 0、零诊断，
公理均在标准三公理内。两个三维闭球沿球面粘合并取反向边界参数的非空实例已通过，内部范数 1/2 的点实际移到其负点。
九项既有输入另行审计通过；`InteriorAtlas` 已有无边模型转换，旧审计中的该项缺口已过时。
本层只完成拓扑封口比较；有限 PL 柄分解、一般光滑柄附着与角光滑化、PL 附着圆/环带及框架光滑化、
任意光滑拓扑二球面的微分标准化及有限归纳装配仍是明确义务。未新增结论型假设或 PLSmoothing 接口，
未证明紧致光滑化端点，也未改动逼近阶段的非紧陈述。完整证据与逐项签名见 HANDOFF_CODEX_S.md 最末节。

**S vertex/edge geometric layer (2026-09-19; integration replay accepted):**
The four new derived-neighborhood modules construct finite disjoint vertex
balls, actual PL edge prisms with exact attaching end disks, the intrinsic
boundary trace of every new face cell, and the actual adjunction-space
homeomorphism onto the next graph-subcomplex neighborhood, fixing the lower
space. The input is a finite combinatorial three-manifold with boundary;
no hSchoenflies or assumed handle decomposition is used. Eight declarations,
23 critical reuse entries and all 13 environment linters per module passed;
all checks and the nondegenerate tetrahedron graph-cycle fixture exited 0
with zero diagnostics and only standard axioms. Index-two/index-three product
pairs and global finite-stage assembly remain open, followed by the smooth
attachment/framing/corner and two-sphere classification obligations above.
The compact smoothing endpoint and unrestricted approximation scope are
unchanged. Exact statements and evidence are in the final S handoff section.

**S triangle two-handle layer (2026-09-19; independently accepted):**
Six fresh modules, all eight nonautomatic declarations (one private), 29
critical reused declarations and nine declarations of the actual
four-simplex-boundary model pass the independent integration audit with
13 linters, standard foundational axioms and zero diagnostics. The actual
triangle cell in finite closed K has its PL disk-prism and exact annulus
trace, intrinsic boundary embedding, product framing and old-space-fixing
successor adjunction. Three distinct points are explicitly checked on one
framing fiber. Lean +548/-0 including six root imports; receipt:
.lake/verified-nineteenth-lane-delivery-20260919.json. Boundary-triangle caps
remain open. S's 78d96386b maximal-cell sphere attachments are independently
accepted below; S continues finite face ordering and actual stage assembly.
Smooth attachment/framing/corners, smooth sphere classification
and compact smoothing are not claimed complete.

**S maximal-cell and three-handle layer (2026-09-19; independently accepted):**
Two fresh modules, all four nonautomatic declarations, twelve distinct
critical reused declarations and nine declarations of the actual tetrahedral
model pass the independent integration audit with 13 linters, standard axioms
and zero diagnostics. The maximal-cell trace equals its whole intrinsic
boundary; its actual sphere attachment fixes the old neighborhood and has
the exact successor carrier. The four-simplex-boundary model verifies a new
interior center point outside the old carrier and distinct boundary images.
Lean +156/-0 including two root imports; receipt:
.lake/verified-twentyfirst-lane-delivery-20260919.json. S's finite face-ordering
and neighborhood-filtration delivery 73a6d1984 is queued for independent
acceptance. S continues actual handle-map assembly along that sequence;
smooth attachment/framing/corners and sphere classification remain open.
Compact smoothing is not claimed complete.

### Phase 3：A′ `PLApproximationManifold 3` 的经典链（Moise §17, §21–28, §30–36）

具体计划（分章定理清单、拟定 Lean 陈述、车道、验收）在 `PHASE3_APPROXIMATION_PLAN.md`（2026-09-12 起草，
通读 Moise §2–5、§7–8、§17、§21–28、§30–36 后写成）。要点：

- 终点只有一条定理 `plApproximationManifold_three : PLApproximationManifold.{u} 3`；A′ → A → 拼接桥 → 图册已证，
  Phase 3 结束时补两条无条件推论 `plApproximation_three`、`exists_chartedSpace_hasGroupoid_plGroupoid_three` 并做公理审计。
- A′ 是 Moise 36.1 取 `U = M₁` 的情形，必须覆盖非紧致 `M₁`；推导顺序 35.1 → 35.2 → 36.1（穷竭 + 不变域）。
- 原始六类数学工作（非当前任务分派）：F 基础（多面体/细分/公共细分/PL 映射单纯化/link 唯一性/正则邻域/一般位置/穷竭/T1、T2）、
  H 同调与曲面（§21–22、23.14–19、28.11）、S Schoenflies（2D 输入 3.3/3.6/5.3/5.4/10.8 → §17 → 23.9–11）、
  C 覆盖/环定理/环带/实心环面（§24–28 关键子集；27.5 Dehn 引理与 28.5, 28.12–18 不在关键路径）、
  I 插值与逼近（§30–34）、E 终局（不变域移植、§35–36、端点）。
- 原始规模/工期估算保留在详细计划的历史分解中，不作当前剩余工作或完成比例的依据。
- 拓扑不变域定理按 classification-of-surfaces 的 `Topology/InvarianceOfDomain.lean`（813 行，维数无关）单文件移植。
- 与光滑 Schoenflies 负责人的接口见该文件 §7：本链自证 PL 版（§17），其证明确实依赖平面多边形 Schoenflies（3.6）；
  不消费光滑版；光滑版若要经 PL 版导出需 Phase 2 级别的 PL/光滑比较。

## 6. 验证记录

- 2026-09-12（Phase 3 车道 F 首轮，工作树 `D:\differential-geometry-moise-plan`，分支 `codex/moise-smoothing`）：新增五个模块
  `Polyhedra.lean`（`IsPolyhedron`、单形是 H-多面体、有限复形的底空间是多面体）、`Barycentric.lean`（重心权唯一性、
  `openSimplex`、载体面、面的极端性、复形中开面不交、`weights` 及其仿射性）、`Subdivision.lean`（`IsSubdivision`，
  粗复形的单形是所含细单形之并）、`Derived.lean`（旗、任意内点的导出细分 `derived` 是 `Geometry.SimplicialComplex`，
  `barycentricSubdivision`，`IsSubdivision`）、`Mesh.lean`（重心细分网格 ≤ N/(N+1)，迭代得任意细的细分
  `exists_isSubdivision_diam_lt`）。每个模块用 Phase 1 配方在共享检出的构件上逐模块检查（`lean` 直接调用，
  LEAN_PATH 取共享检出的包与构建库，新 olean 写入共享构建库，脚本 `check-f.ps1`），零错误零警告；
  十个端点（含 `derived_isSubdivision`、`barycentricSubdivision_isSubdivision`、`exists_isSubdivision_diam_lt`）
  `#print axioms` 只含标准公理。未登记根聚合（整合仍按负责人指示推迟）。
  同日第二批：`Star.lean`（有限复形中闭星是底空间内的邻域 `closedStar_mem_nhdsWithin`；逐单形仿射的映射分段仿射
  `isPiecewiseAffineOn_space_of_forall_face`；仿射无关集上的赋值延拓为仿射映射）、`SimplicialMap.lean`
  （载体面 `carrierFace`、顶点映射的单纯延拓 `simplicialMap`、单纯同构给出 PL 同胚 `isPLHomeomorphOn_simplicialMap`）、
  `RegularNeighborhood.lean`（`regularNeighborhoodIn`、二次重心细分 `secondDerived`、`regularNeighborhood K A`
  及其邻域性质 `regularNeighborhood_mem_nhdsWithin`）、`SimplexBall.lean`（仿射无关有限集的凸包是 PL 球
  `isPLBall_convexHull_of_affineIndependent`）。同样逐模块检查零错误零警告，十七个端点公理审计只含标准公理。
  推送至 `origin/codex/moise-smoothing`。
- 2026-09-12（车道 F 第三批，胞腔复形）：`Arrangement.lean`（有限族仿射泛函的符号向量胞腔：开/闭胞腔、符号序 `SignLE`、
  吸收引理 `combo_mem_openCell`、边界点的严格坐标、闭胞腔闭且凸、沿开胞腔点的线段延伸、射线出口点存在
  `exists_exit_of_mem_openCell` 与唯一 `exit_unique`）、`CellComplex.lean`（紧致"胞腔闭"集 `P` 的胞腔族、
  胞腔旗、`cellDerived l P` 是 `Geometry.SimplicialComplex`（仿射无关性由顶胞腔的严格坐标给出；交集公理由
  "过一点的旗唯一"给出，其顶系数由射线出口点唯一性决定）；`space_cellDerived`；胞腔闭子集是单形之并）、
  `Triangulation.lean`（任意有限族 H-多面体被同一个复形三角剖分且各为子复形之并
  `exists_simplicialComplex_of_forall_isHPolytope`；F1.2 `IsPolyhedron.exists_simplicialComplex`；
  F2.3 `exists_isSubdivision_subcomplexes`；公共细分 `exists_common_subdivision`）、
  `PiecewiseAffineSimplicial.lean`（F3.1 正命题：有限复形上的分片仿射映射在某细分的每个单形上仿射
  `IsPiecewiseAffineOn.exists_isSubdivision_affineOn_faces`）。逐模块检查零错误零警告；
  `#print axioms` 仅 `propext`、`Classical.choice`、`Quot.sound`。

- 2026-09-13（车道 F 第四批，link 唯一性 F3.3）：`PLHomeomorph.lean`（PL 同胚复合/逆/转移）、`Cone.lean`（径向投影、锥底、
  顶点 link 的径向单射性）、`SimplicialImage.lean`（单纯映射像复形）、`RadialProjection.lean`（伪径向投影是 PL 同胚
  `exists_isPLHomeomorphOn_of_radial`）、`LinkSubdivision.lean`（顶点 link 在细分下 PL 不变）、`SimplexBoundary.lean`
  （单形边界复形、`isPLSphere_biUnion_erase`、任意小单形邻域）、`LinkEuclidean.lean`
  （`isPLSphere_geometricLink_of_mem_nhds`：`finrank E = n+1` 且 `K.space ∈ 𝓝 p` ⟹ 顶点 link 是 PL `n`-球面）。
  逐模块检查零错误零警告；九个端点 `#print axioms` 仅标准公理（`.lake/scratch/AuditF5.lean`）。

- 2026-09-13（车道 F 第五批，锥与锥延拓 F3.4）：`ConeComplex.lean`（锥复形 `coneComplex`、`closedStar_eq_coneComplex_space`）、
  `ConeBase.lean`（`affineIndependent_insert_iff`、锥底在细分下稳定、`isConeBase_simplexBoundary`）、`ConeExtension.lean`
  （`exists_isPLHomeomorphOn_coneComplex`：锥底间 PL 同胚的锥延拓，保射线）、`StdSimplexCone.lean`
  （标准单形是中心对边界的锥；`IsConeBase.isPLBall_of_isPLSphere`、`isPLBall_closedStar`、
  `IsCombinatorialManifold.isPLBall_closedStar`）。逐模块检查零错误零警告；七个端点 `#print axioms` 仅标准公理
  （`.lake/scratch/AuditF6.lean`）。

- 2026-09-13（车道 F 第六批，T1 组合流形的 PL 图册）：`OpenStar.lean`（顶点开星、锥描述、相对开性、
  星同胚 `exists_starHomeo`）、`StdChart.lean`（标准单形开单形与 `EuclideanSpace ℝ (Fin (n+1))` 中开集
  `stdTarget` 之间的仿射投影/提升）、`VertexChart.lean`（顶点图卡 `vertexChart`、图册 `combinatorialChartedSpace`、
  `HasGroupoid _ (plGroupoid (n+1))`、图卡与逆图卡在环境坐标下分片仿射；`combinatorialManifoldPLStructure_succ`）、
  `CombinatorialZero.lean`（`n = 0`；`combinatorialManifoldPLStructure : ∀ n, CombinatorialManifoldPLStructure n`）。
  逐模块检查零错误零警告；`#print axioms` 仅标准公理（`.lake/scratch/AuditF7.lean`、`AuditF8.lean`）。
  这样 Phase 1 的 T1、T2 接口都已由 Phase 3 车道 F 证明：`combinatorialManifoldPLStructure : ∀ n, CombinatorialManifoldPLStructure n` 与 `plManifoldTriangulation : ∀ n, PLManifoldTriangulation n`（`Gluing`/`ChartPiece`/`Subcomplex`/`SubdivisionTransport`/`ChartGlue`/`TriangulationExistence`/`StarComplex`/`Combinatorial`，2026-09-13）；`PLManifoldTriangulation n` 增加了 `[Nonempty X]`（空流形没有 `PLTriangulation`，因 `map : ℝ^N → X`）。

- 2026-09-11（Phase 1 第二轮，负责人指示不等完整构建）：`IsPiecewiseAffineOn` 改为基于 `IsPiecewiseAffineWithinAt`
  （`𝓝[s] x`）的定义并重跑整条链；新增 `Manifold.lean`、`Polyhedron.lean`，以及 `Smoothing.lean` 中的
  `PLSmoothingModel`/`plSmoothing_of_plSmoothingModel`。九个模块逐个 `lake env lean` 加 lakefile 选项检查零错误零警告；
  端点与主要引理（含 `plSmoothing_of_plSmoothingModel`、`piecewiseAffineProperty_localInvariantProp`、`isPL_id`、
  `isPLAt_iff_of_mem_maximalAtlas`、`isPLBall_stdSimplex`）`#print axioms` 均只含标准公理。
- 2026-09-11（深夜）：`ApproximationManifold.lean` 通过检查；`plApproximation_of_plApproximationManifold`
  与 `AtlasOn.subtypeChartedSpace_hasGroupoid`、`AtlasOn.subtypeRestr_mem_maximalAtlas` 公理审计只含标准公理。

- 2026-09-11：源码审计与路线固定。
- 2026-09-11（Phase 1 首轮）：以下七个模块在本检出用 `lake env lean` 加 lakefile 选项
  （`autoImplicit=false`、`weak.linter.mathlibStandardSet=true` 等）逐个检查，零错误零警告；
  完整根构建仍在进行，故尚未登记到 `DifferentialGeometry.lean`（构建结束后登记并做增量根构建）。
  - `Topology.PiecewiseLinear.Polytope`：`IsHPolytope` 及 `inter`、`inter_preimage`、`image_affineEquiv`、
    `exists_isHPolytope_subset_mem_nhds`。
  - `Topology.PiecewiseLinear.PiecewiseAffine`：`IsPiecewiseAffineOn`；`isPiecewiseAffineOn_of_affine`、`_id`、
    `_of_locally`、`.mono`、`.congr`、`.continuousAt`、`.comp`、`.symm`（PL 同胚之逆）；辅助
    `linear_injective_of_injOn_of_interior_nonempty`、`iUnion_interior_nonempty_mem_nhds`。
  - `Topology.PiecewiseLinear.Groupoid`：`plPregroupoid`、`plGroupoid`、`mem_plGroupoid_iff`、
    `mem_plGroupoid_of_isPiecewiseAffineOn`、`ofSet_mem_plGroupoid`、`ClosedUnderRestriction (plGroupoid n)`。
  - `Topology.Manifold.PartialAtlas`：`AtlasOn G U` 及 `congr`、`empty`、`ofOpenPartialHomeomorph`、`restrict`、
    `transport`、`union`、`chartedSpace`、`hasGroupoid`、`ofChartedSpace`；`ofSet_mem_of_closedUnderRestriction`。
  - `Topology.PiecewiseLinear.Approximation`：接口 `PLApproximation n`（§4.2 的 A）；健全性定理
    `plApproximation_zero : PLApproximation 0`（0 维时接口可满足，说明接口不是矛盾或空洞的；用到
    `IsHPolytope.univ_of_subsingleton`、`isPiecewiseAffineOn_of_subsingleton`）。
  - `Topology.PiecewiseLinear.ChartGluing`：两集合拼接桥 `exists_atlasOn_union_of_plApproximation`
    （度量空间版）与 `_of_metrizable`；有限图卡归纳 `exists_atlasOn_univ_of_plApproximation`；
    `exists_chartedSpace_hasGroupoid_plGroupoid_of_plApproximation`（条件性 Moise 三角剖分：`∃ C, HasGroupoid X (plGroupoid n)`）。
  - `Topology.PiecewiseLinear.Smoothing`：接口 `PLSmoothing n`（B）；端点
    `exists_isManifold_of_plApproximation_of_plSmoothing` 与 `n = 3` 的书中接口形式
    `exists_isManifold_three_of_plApproximation_of_plSmoothing`；健全性 `plSmoothing_zero : PLSmoothing 0`，
    以及由两个 0 维接口实例装配出的**无条件**端点 `exists_isManifold_zero`
    （紧致 T2 的 0 维拓扑流形有同拓扑光滑结构），验证桥 + 归纳 + 装配链在给定接口时确实合成为真定理。
  - `#print axioms`（临时审计文件 import `Smoothing`）：以上端点及 `IsPiecewiseAffineOn.symm/comp`、
    `AtlasOn.hasGroupoid/restrict`、`exists_isHPolytope_subset_mem_nhds` 均只依赖 `propext`、`Classical.choice`、`Quot.sound`。
    条件性完全由签名中的 `PLApproximation`/`PLSmoothing` 假设表达，树中没有新增 `sorry`/`axiom`。

- 2026-09-14（车道 E.0，不变域，工作树 `D:/differential-geometry-moise-e0`，分支 `codex/moise-e0`）：
  四砖已闭合：`Topology/InvarianceOfDomain.lean`（上游解析证明与图卡接口，保留抽象条件签名）；
  `Topology/FixedPoint/NoRetraction.lean`（任意正有限维无收缩，一维连通性，高维球面顶维同调）；
  `Topology/FixedPoint/Brouwer.lean`（任意有限维闭单位球不动点定理及已证实例，含零维）；
  `Topology/InvarianceOfDomainManifold.lean`（七个无未证类参数的最终接口）。
  主端点为 `invariance_of_domain_isOpen_image`、`isOpen_image_of_continuousOn_injOn`、
  `isOpenMap_of_continuous_injective`；另有
  `isOpen_range_of_isOpen_of_continuous_injective_real`、`isOpen_range_of_isOpen_of_isEmbedding_real`、
  `isInteriorPoint_iff_any_chart_real`、`isBoundaryPoint_iff_any_chart_real`。
  模型空间 `E : Type*`、流形宇宙独立，且审计文件显式检查了 `EuclideanSpace ℝ (Fin n)` 的要求形式。
  每砖仅经交接脚本 `check-f.ps1` 串行检查（均 exit=0、零错误零警告），
  `AuditE01`/`AuditE02`/`AuditE03`/`AuditE0`（本车道 `.lake/scratch`）审计只含允许的标准公理；
  七个最终接口、无收缩定理、不动点定理及其实例均只含 `propext`、`Classical.choice`、`Quot.sound`。
  检查点 `8a113f636`、`87d67526b`、`5025cc6f0`、`7723c30c3` 已逐砖推送。
  与交接路线的实现差异：直接复用 `integralSingularHomology_subsingleton_of_contractible`，省去约化同调桥；
  流形证明用一个源图卡与已有模型到流形开像定理；追加四个显式无条件的实模型接口。
  原生移植来源为 mccorvie/classification-of-surfaces@e3c7230，原版权/作者声明、Apache-2.0 全文和修改记录
  保存在 `docs/third_party/`。无新增证明债、注释、诊断命令或资源选项。
  最终同步已抓取并纳入 F 分支 `6b67ac39f`；为同时保留逐砖发布历史与禁止 force-push 的约束，采用
  `5770071c3` 将 F 更新合入 E.0。普通 rebase 会重写已发布的四个检查点，其本地结果未发布，已恢复到
  内容相同且保留双方历史的合并节点。未修改 F 工作树或分支，未合并 E.0 到 F，未运行 `lake build`，
  未登记根聚合；E.0 数学端点完成，S.1、M.3、E.3/E.4 自身义务继续由各自车道承担。

- 2026-09-14（S 车道前半，`D:/differential-geometry-moise-s`，`codex/moise-s`）：
  - S0.1：`a940dc7e4` vendoring `ClassificationOfSurfaces` 的 16 个平面 PL 模块，来源固定为
    `e3c7230fe78d7b056a415d9ecae6f77887046b32`，Apache-2.0；保留注释、版权头、命名空间和原始文档。
    每处 import/API 漂移与 13 条获准保留的原始纯风格警告均记录于 `External/ClassificationOfSurfaces/VENDOR.md`。
    按依赖序逐模块检查 exit=0，AuditS1 仅标准三公理。
  - S0.2/P.1：`81b0310b5` 的 `PlanarSchoenflies.lean` 与 `SimplexFrontier.lean` 证明
    原生 PL 1-球面与 `PolygonalCircle` 的双向转换，以及 `isPLBall_of_isPLSphere_one` 的有界 PL 2-球填充。
    `72fb0bbd3` 补齐完整 3.7：`exists_isPLHomeomorphOn_straighten` / `_of_isPLSphere_one` 给全平面
    双向 PL 的相对整直，固定指定开集外；原 `_on_closedRegion` 签名保留为推论。AuditS10 十项仅标准三公理。
    自由三角形移动及剥离归纳的出处和修改记录已补入 VENDOR。
    P.3 已有三角剖分多边形盘的两个几何自由三角形，P.5 已有多边形 θ-图区域分解；一般相对胞腔删除、
    任意弧 4.4 和 Problem 4.1 未闭合。第二批只提供 6.2–6.3 的嵌入逼近，未覆盖 P.4 的 10.8，故没有导入。
  - S.1：`a04d993c4` 整合 E3 的 frontier/边界点球邻域证明，适配 F 的规范边界不变性，
    `PolyhedralBoundary.lean` 与 `FrontierBoundary.lean` 提供所有正维欧氏形式和流形形式。
    AuditS3 含显式 ℝ³ 签名，六项均仅标准三公理；没有把重用 E3 的代码报告为独立新证明。
  - P.2：`ff7fc67ca` 的 `BallFrontier.lean` 证明实际 frontier 上的 PL 球边界延拓，
    `n = 1` 给平面 2-球形式，并证明 PL 球 frontier 的球面性；AuditS6 四项仅标准三公理。
  - S.2 **partial**：`8a6995d74` 的 `PushProperty.lean` 证明 17.7；`b29c69f17` 的
    `AmbientExtension.lean` / `ConeIsotopy.lean` 给相对多面体邻域中的顶点移动及锥顶连续路径移动；
    `8c4d4fe91` 的 `SimplexBoundaryImage.lean` / `SimplexPush.lean` 闭合 17.4 的任意四面体面推送。
    核对并修正计划原先的邻域写法：使用 `C \ J`，不取闭包，J 是盘的内在边界圈而非环境 frontier D。
    `e3686847e` 增加固定 frontier 的恒等延拓、交集保持的 PL 拼接及两侧锥环境延拓，
    三个新声明连同全平面相对定理通过 AuditS11。17.5 尚缺四面体边界星的锥交集、frontier、
    支撑控制几何条件和保留指定三角形的删除归纳；17.6、17.8 仍依赖它。无占位证明债。
  - 最终 13 个 S 原生模块和 2 个同步的 F 半空间模块逐一复查 exit=0、零警告；
    AuditS12 在同一环境中审计 60 个不同声明，全部仅标准三公理、exit=0。
    日志为 `.lake/scratch/final2-*.log` 和 `audit-final2-s.log`。未运行 lake build，未登记根聚合。
    最终同步 F 至 `b66f6b5b0` 时使用普通合并保留已发布检查点，未重写历史或 force-push，
    未将 S 分支合并到其它分支；精确消费状态和 §17.4–17.12 拟定陈述见 `PHASE3_APPROXIMATION_PLAN.md` §4.1–4.2。

- 2026-09-15（S 车道继续，工作树与分支保持不变）：
  - 平面链：`4fffc8f99` 将保留指定三角形接入删除归纳；`91172ea49` 证明 PL 球/球面非空、
    有限剖分的纯维性及同维欧氏 PL 球的内部稠密性，并由此识别任意原生平面 PL 圆盘为多边形闭区域。
    `exists_isPLHomeomorphOn_remove_geometricallyFree_triangle` 给整盘的精确删除像和剩余盘球性。
    `80fceca30` 的 `exists_isPLHomeomorphOn_straighten_to_face` 接受任意原生剖分及任意指定三角形。
  - 17.5 的几何准备：`21401b31b` / `01974cece` 实际构造顶点星的两侧锥并证明交集、frontier 和支撑；
    `afc350cbe` 产生与 D 兼容且闭星足够细的边界剖分，以及星到对面的单纯坐标。
    `aebd603dd` 的 `SimplexAffine` / `SimplexCornerChart` 给真正二维欧氏坐标、实际边界和开星对应；
    环境延拓保持整个四面体，逐点固定对面与给定邻域外，并给任意边界子集的精确图像公式。
  - `80fceca30` 的 `SimplexDisk`：对整个 D 位于一个原始顶点开星内的情形，
    `exists_isPLHomeomorphOn_straighten_to_face_in_simplex_vertex_star` 将 D 整直到任意指定剖分三角形，
    保持四面体并固定对面及邻域外；任意 PL 圆盘的推论自行产生该三角形。
    `8fa61de34` 的 `StarSubdivision` 证明闭星覆盖控制在任意后续细分下保持。
  - 真实剩余义务：跨星圆盘的局部自由三角形删除须控制接缝并证明整个圆盘的删除像，再作保留三角形归纳。
    星内交集未必是盘，上游的整盘删除不能直接用于它。完整 17.5、17.6、17.8 及 S.2 仍为 partial；
    P.3 的一般 17.2/17.3、P.4 的 10.8、P.5 的任意弧版本仍未闭合，第二批仍不触发。
  - 验证：每层原生检查 exit=0、零警告；AuditS13–S21 的端点仅标准三公理。
    `9c9002426` 纳入 F 至 `8c1ce1d4f` 时复查 39 个修改/相关模块、AuditS18 审计 127 项；
    最后抓取并合入 F 至 `d0902b2cd`，保留 S 已完成的 P.1/P.2，整合 F 的横截弧剖分、边界和降阶输入。
    最后复查 12 个模块均 exit=0、零警告；AuditS22 去重审计 198 个声明，仅标准三公理、exit=0；
    日志为 `final3-*.log` 与 `audit-final3-s.log`。
    所有同步均为 S 上的普通合并，未改其它车道源码或重写已发布历史；未运行 lake build，未登记根聚合。
    逐层出处、调整和验证记录位于 `External/ClassificationOfSurfaces/VENDOR.md`，本轮未修改 vendor Lean 源码。

- 2026-09-15（Phase 3 车道 C：Moise §24 C.1–C.3，工作树 `D:\differential-geometry-moise-e3`，分支 `codex/moise-e3`）：
  `CoveringLift.lean` 闭合 24.1–24.4：PL 球的单连通与局部道路连通、覆盖唯一提升、基本群映射单射、闭路提升判据、
  单值作用的稳定子/像子群识别、连通覆盖的纤维基数等于像子群指标；九个端点检查 exit=0、零 warning，AuditC1
  仅 `propext`、`Classical.choice`、`Quot.sound`，源码提交 `2df0546f5`。`DoubleCoverComplex.lean` 从有限复形上的
  `SimplicialBoolCocycle` 构造 `BoolCocycle` 二重覆盖，证明纤维基数为 2，并以连续截面双向识别上边界，得到
  `connectedSpace_iff : ConnectedSpace TotalSpace ↔ ¬ IsCoboundary`；二十三个端点检查 exit=0、零 warning，AuditC2
  仅标准三公理，源码提交 `364fbe752`。`CoveringTriangulation.lean` 对任意有限纤维覆盖逐基单形作唯一提升，以纤维顶点
  的标准基实现有限复形，粘合出 `coveringSpaceHomeomorph`；投影逐单形等于仿射映射并满射到一个基单形，顶点 link 的
  `coveringVertexLink_isGlueIso` 给出任意维 `IsCombinatorialManifoldWithBoundary` 保持，最终端点为
  `exists_lift_simplicialComplex`。十六个端点检查 exit=0、零 warning，AuditC3 仅标准三公理，源码提交 `f7e70bc61`；
  直接逐单形提升比 Moise 24.6 的均匀覆盖细分路线更强，未弱化结论。
  D4 首次复用审计逐条记录如下，全部只依赖标准三公理：AuditC1Reuse 的
  `IsPLHomeomorphOn.homeomorph`、`Convex.contractibleSpace`、`Convex.locallyPathConnectedSpace`、
  `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`、`IsCoveringMap.existsUnique_continuousMap_lifts`、
  `IsCoveringMap.continuous`、`IsCoveringMap.injective_path_homotopic_map`、`FundamentalGroup.map`、
  `FundamentalGroup.map_apply`、`IsCoveringMap.fundamentalGroupMulAction`、`IsCoveringMap.monodromy`、
  `IsCoveringMap.liftPathQuotient`、`IsCoveringMap.map_liftPathQuotient`、`IsCoveringMap.monodromy_eq_of_map_eq`、
  `IsCoveringMap.liftPath`、`IsCoveringMap.liftPath_zero`、`IsCoveringMap.liftPath_lifts`、
  `MulAction.index_stabilizer_of_transitive`；AuditC2Reuse 的 `BoolCocycle.isCoveringMap_proj`、
  `BoolCocycle.toFiberBundleCore`、`BoolCocycle.sectionCoord`、`BoolCocycle.sectionCoord_change`、
  `BoolCocycle.isLocallyConstant_sectionCoord`、`Covering.exists_section_of_not_connected_double_cover`、
  `Covering.not_connected_of_double_cover_section`、`FiberBundle.isClosedMap_projection_of_finite`、
  `Bundle.Trivialization.preimageSingletonHomeomorph`、`FiberBundle.continuousAt_totalSpace`、
  `FiberBundle.mem_trivializationAt_proj_source`；AuditC3Reuse 的 `IsCoveringMap.exists_unique_lift_of_isPLBall`、
  `PiecewiseLinear.IsCoveringMap.exists_unique_lift_of_face`、`Covering.t2Space_of_isCoveringMap`。整条 C.1–C.3 链未 import、
  未传递经过含 `sorry` 的 `Topology/Homology/HurewiczLowDegrees.lean`。同步时保留上游 `BoundaryInvariance.lean` 的五个
  边界/前沿不变性端点并合入 `polyhedralBoundary`，修正剩余旧实例语法后该模块检查 exit=0、零 warning；未运行根构建，
  未登记根聚合。E3.2/E3.3 仍因非紧局部有限表示层缺口搁置，详见 `PHASE3_APPROXIMATION_PLAN.md` 的 F6.3/E.2/E.3/R9。

- 2026-09-15（F 车道，§12.1 的 E.3 条件版检查点）：`Transition361.lean` 明确定义 `Moise352`
  与 `IsPLHomeomorphInto`。逆映射按像中每点的 `IsPLWithinAt` 表述，避免空源、非空目标时总逆函数不存在；
  `isPLHomeomorphInto_iff_exists_inverse` 证明源非空时与原单个总逆映射形式等价。
  `Moise352.exists_approx_of_isOpen` 用 F6.3 对整个开集一次应用 35.2，单独处理空集；
  `IsPLHomeomorphInto.isOpen_image` 从 E.0 推出开像。聚焦检查 exit=0、零 warning，AuditF115
  十个声明均仅 `propext`、`Classical.choice`、`Quot.sound`。完整 36.1 陈述在同一审计文件中通过类型检查；
  像集等式尚待穷竭论证，E.3/E.4 尚未完成，35.2 仍只是显式命题。未运行 lake build，未登记根聚合。

- 2026-09-15（F 车道，砖 15）：`Transition361.lean` 闭合 `exists_plh_approx_of_isOpen`，条件仅为
  显式 `Moise352 3`；一般正维版本为 `Moise352.exists_approx_image_eq_of_isOpen`。F6.3 塔提供紧致穷竭，
  局部有限的阶段前沿与连通分支分别给连续正误差控制；对整个 U 一次应用 35.2 后，紧致路径被穷竭捕获，
  前沿分离推出像集相等。此论证不需要增加阶段连通假设。`IsPLHomeomorphInto.image_polyhedralBoundary`
  从 M.3 和不变域给精确边界像等式；更一般的紧集前沿等式先在拓扑层证明。
  该模块聚焦检查 exit=0、零 warning；AuditF116 审计十五个声明，全部仅标准三公理。
  36.1 已完成条件版；35.2 仍未证，端点砖 16 随后接入。未运行 lake build，未登记根聚合。

- 2026-09-15（F 车道，砖 16）：`Endgame.lean` 的 `plApproximationManifold_three_of_moise352`
  证明 `Moise352.{u} 3 → PLApproximationManifold.{u} 3`。在 U = univ 使用 36.1，像集相等给满射，
  不变域给开映射，由连续双射组装同胚；保留原端点的任意连续正误差与两侧 PL 流形实例。
  `Endgame` 聚焦检查 exit=0、零 warning；AuditF117 连同砖 15 接口共十六项，全部仅
  `propext`、`Classical.choice`、`Quot.sound`。E.3/E.4 均为条件版 done，35.2 本身没有被证明。
  下一项按 §12.2 处理 F5.2 的整体片与载体约束扰动。未运行 lake build，未登记根聚合。

- 2026-09-15（F 车道，F5.2 的 §12.2 路线审查）：`CarrierPerturbation.lean` 证明最小载体约束的刚性。
  顶点的 `carrierFace` 是单点；当原顶点映到目标顶点，任何仍在原载体仿射包内的顶点像都等于原值，
  `simplicialMap_eqOn_of_mem_affineSpan_carrierFace` 给整个单纯映射相等，双点集也精确不变。
  `not_disjoint_doublePointSet_vertices_of_mem_affineSpan_carrierFace` 证明既有顶点双点不能移离目标顶点集。
  六个声明聚焦检查 exit=0、零 warning；AuditF118 连同砖 15/16 共二十二项全部仅标准三公理。
  此结果是 §12.2 固定最小载体路线的障碍证明，不是 F5.2 正规形式的存在证明。按交接约定在数学缺口处汇报，
  F5.2 保持 partial，等待允许跨出低维载体且保持目标片内兼容性的设计；详见交接 §14 和风险 R10。

- 2026-09-15（C 车道，L.1 定义层）：工作树 `D:\differential-geometry-moise-e3`、分支 `codex/moise-e3` 的
  `DerivedNeighborhoodRetraction.lean` 以导出细分的重心坐标质量、矩与投影显式构造子复形导出邻域到子复形的强形变收缩，
  `derivedNeighborhoodFundamentalGroupInclusionEquiv_apply` 识别所得基本群同构为实际包含映射的 `FundamentalGroup.map`。
  `LoopTheorem/SingularCell.lean` 定义 `SingularTwoCell`、自由环的 `FreeLoop.conjugacyClass`、顶点碰撞复杂度与
  `NormalSystem`；`K₁` 为保留像单形的相对导出邻域且载体等于标准导出邻域，`B₁` 为边界中环复形的导出邻域；
  `NormalSystem.complexity_eq_zero_iff_isNonsingular`、`NormalSystem.loopConjugacyClass_eq_of_connector` 与
  `NormalSystem.loopConjugacyClass_disjoint_normal` 分别闭合复杂度零、连接道路无关性与正规子群不交条件。
  两个模块的聚焦检查均 exit=0、零 warning；AuditL1 对 51 项端点及复用声明审计 exit=0，全部公理闭包均包含于
  `propext`、`Classical.choice`、`Quot.sound`。本砖首次复用并逐条审计的拓扑/相对导出声明为
  `exists_basedCircle_free_homotopic`、`basedCircleHomotopyTrack_commutes`、
  `fundamentalGroupChangeBasepoint_connector`、`fundamentalGroupMulEquivOfHomotopyEquiv`、
  `faces_subset_relativeDerivedNeighborhood`、`relativeDerivedNeighborhood_faces_finite`，均仅标准三公理；未经过
  `Topology/Homology/HurewiczLowDegrees.lean`。源码提交 `d81e1897c`；L.1 无未闭合书中步骤，未运行根构建，未登记根聚合。

- 2026-09-15（S 车道 S.3 / P.3 一般 17.2 / S.5 当前交付，数学提交 `08ee37003`）：
  `ConvexStraightening`、`ConeStraightening`、`PlanarDiskGluing` 无条件证明 17.9–17.11，
  保留每个凸开邻域外恒同及盘的内在内部；线性层形式精确匹配 F 的冻结接口。
  `FreeDiskCell` 对任意有限维实赋范空间的共同有限三角剖分证明一般盘分解的两个不同自由胞腔，
  并给避开一个指定胞腔的推论；17.3 的指定真盘子复形版本仍未证。
  `SchoenfliesFoundations.lean` 的 `schoenflies_input` 填满原样保留的
  `SchoenfliesInput` 四字段，无未证输入。S.4 由 F 车道实现。
  `SchoenfliesManifold`（23.9）与 `PushManifold`（23.10）按授权显式接受完整 17.12 的陈述，
  给顶点开星内填充与保持精确相对邻域的推移；该参数仍待 F 的生产者交付后解除。
  `BallGluing` / `BallGluingManifold`（23.11）已无条件完成，包含两球位于不同顶点星的有限组合流形形式。
  最终 9 个端点模块检查 exit=0、零警告；AuditS61 精确核对 F 接口，AuditS62 的 16 个声明仅标准三公理。
  源码散列与日志见 `.lake/scratch/S3-P3-S5-VERIFICATION.json`；各层来源与差异见
  `External/ClassificationOfSurfaces/VENDOR.md`。没有修改 vendored Lean、没有 lake build 或根聚合登记。
  最后文档提交前已 fetch 并 merge `origin/codex/moise-integration`，保留所有已发布检查点。

- 2026-09-15（H 车道 H.2a，任意线性细分与 PL 定向不变性）：
  已通过整合分支取得 F 的 `PLBallSphere.lean` 连通性 API；本次合并的远端端点为 `b9a2cb2ca`，
  H 的合并提交为 `4be28804d`，没有复制、cherry-pick 或直接合并其它车道。
  `AffineOrientation.lean`、`ManifoldConnectivity.lean`、`Orientation.lean` 串行聚焦检查均 exit=0、零警告
  （分别 12.9、10.9、30.8 秒），使用原始 `check-f.ps1` 写入共享库，每次启动前核对主机进程配额。
  正向细分以仿射坐标矩阵行列式的符号传递顶维定向，反向用每个旧顶维单形内的对偶图连通性证明局部比较符号恒定；
  对偶图连通性经顶点 link 的维数归纳取得。由此闭合
  `isOrientable_iff_of_isSubdivision`、`isOrientable_iff_of_isPLHomeomorphOn`、
  `isOrientable_of_isPLBall`、`isOrientable_of_isPLSphere`、`isOrientable_faceStarComplex`、
  `exists_unique_coherentOrientation_comparison_faceStarComplex`，包含零维。
  细分和 PL 不变性保留源复形的组合流形假设；球面接口维数为 `IsPLSphere n → IsOrientable n`。
  “恰两个定向”指统一顶点序后的所有顶维符号相同或互为负号，不是原始 `CoherentOrientation` 结构仅有两个元素。
  `AuditH2aIntegrated` 对 53 项核心声明逐项审计 exit=0；`AuditH2aIntegratedReuse` 对下列 22 项复用声明逐项审计
  exit=0，所有闭包均为 `propext`、`Classical.choice`、`Quot.sound`：
  本库 `Topology.SimplicialComplex.mem_geometricLink_singleton`、`finite_geometricLink_faces`；
  PL 层的 `exists_face_superset_card_eq_of_isPLBall_or_isPLSphere`、`exists_face_superset_card_eq_of_isPLBall`、
  `IsPLBall.nonempty`、`IsPLSphere.nonempty`、`IsPLBall.isCombinatorialManifoldWithBoundary`、
  `IsPLSphere.isCombinatorialManifold`、`IsCombinatorialManifoldWithBoundary.card_le_one`、
  `IsPLBall.isConnected`、`IsPLSphere.isConnected`、`isConnected_stdSimplexBoundary`、
  `faceStarComplex`、`faceStarComplex_faces_finite`、`IsCombinatorialManifoldWithBoundary.isPLBall_faceStarComplex`、
  `restrict`、`restrict_faces_finite`、`restrict_space_of_eq_biUnion`、`IsSubdivision.convexHull_eq_biUnion`、
  `exists_isGlueIso_of_isPLHomeomorphOn`、`IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn`；
  Mathlib 的 `AffineIndependent.card_le_card_of_subset_affineSpan`。
  未经过 `Homology/HurewiczLowDegrees.lean`，未运行根构建，未登记根聚合。
  H.2a 无未闭合端点；H.2b 的定向上循环仍待按交接 §7.3 构造，H.6/H.4a/H.5 不在本次闭合范围。

- 2026-09-15（H 车道 H.2b，闭星局部定向上循环）：
  `DerivedCarrier.lean` 给重心细分顶点与原面载体的对应及旗标公共上面；
  `Orientation.lean` 的 `CoherentOrientation.restrict` / `IsOrientable.of_le` 推广到包含零维的任意 `n`；
  `OrientationCocycle.lean` 先统一局部顶点序，再在公共顶维单形上比较每个非空面闭星的相干定向。
  比较符号的选择无关性由公共闭星的对偶连通性证明，三角形恒等式在同一顶维单形上验证；
  没有使用旧“非顶维边取 0”的构造。构造层提交 `85cd6e095`。
  `orientationCocycle_isCoboundary_iff` 双向证明上边界当且仅当全局可定向：
  正向由上边界的顶点符号翻转局部定向并验证所有余维一面的边界抵消，反向限制全局定向并取局部比较符号。
  `exists_orientationCocycle_of_not_isOrientable` 从 H.2a 的闭星可定向性选局部族，给 C.4 所需的非上边界上循环。
  三个端点对任意 `n`、有限维实赋范环境、有限复形成立，没有连通性、正维或公开 `DecidableEq` 假设。
  三个目标模块均聚焦检查 exit=0、零警告；`AuditH2bReuse` exit=0，逐项核对 12 项核心声明与 12 项复用声明，
  公理闭包全为 `propext`、`Classical.choice`、`Quot.sound`，并检查三个端点的完整签名。
  核心审计为 `CoherentOrientation.restrict`、`IsOrientable.of_le`、`carrierFace_centroid`、
  `carrierFace_mem_of_mem_barycentricSubdivision`、`centroid_carrierFace_of_mem_barycentricSubdivision`、
  `exists_face_superset_carrierFaces_of_mem_barycentricSubdivision`、`pair_centroid_mem_barycentricSubdivision`、
  `faceStarComplex_antitone`、`faceCofaces_faceStarComplex_self`、`orientationCocycle`、
  `orientationCocycle_isCoboundary_iff`、`exists_orientationCocycle_of_not_isOrientable`。
  复用审计为 `SimplicialBoolCocycle`、`SimplicialBoolCocycle.IsCoboundary`、`carrierFace`、`carrierFace_mem`、
  `mem_openSimplex_carrierFace`、`face_eq_of_mem_openSimplex`、`centroid_mem_openSimplex`、
  `centroid_mem_openSimplex_of_mem_faces`、`IsFlag.subset_or_subset`、`IsFlag.exists_top`、
  `mem_faceStarComplex_faces_of_subset`、`faceStarComplex_faces_subset`，均来自整合后已有 PL 源码。
  H.2b 要求的三个端点均闭合；C.4 的二重覆盖流形及其可定向性没有在本次代做。
  未经过 `Homology/HurewiczLowDegrees.lean`，未运行根构建，未登记根聚合；H.6/H.4a/H.5 顺序和目标不变。

- 2026-09-15（H-M2 开邻域几何层中间检查点）：`SubcomplexNeighborhood.lean` 聚焦检查 exit=0、零警告。
  19 项新声明、8 项复用声明在 `AuditNightHM2Neighborhood.lean` 逐项审计，均仅标准三公理。
  `AuditNightHM2Reuse.lean` 另外逐项预审计了 PL 的质量、投影、同伦、质量与矩的过滤和公式、
  投影的凸包归属与权重公式、投影固定子复形、质量与矩连续性、细分过滤面、
  `derivedNeighborhoodStrongDeformationRetract`、细分顶点的重心表示，共 14 项；
  原生 Homology 的 `subspaceSmallShortExact`、`smallChainHomologyIso`、
  `augmentedSubspaceSmallShortExact`、`augmentedSmallChainHomologyIso`、
  `reducedMayerVietorisConnectingMap_coefficient_naturality` 共 5 项，均仅标准三公理。
  两个审计文件保留在 H 工作树 `.lake/scratch`。闭导出邻域的已有形变收缩不能直接充当开覆盖；
  此处实际构造了正重心质量开邻域，并证明交子复形的邻域等于邻域之交。
  H-M2 的同调正合性与自然性搬运仍待完成，没有将几何层记作 28.11 已证明。

- 2026-09-15（H-M2，子复形 Mayer–Vietoris 与 28.11 闭合）：
  几何层提交 `11826f868`；随后 `MayerVietorisSubcomplex.lean` 的
  `exists_mem_inter_of_map_eq_zero` 对有限复形的两子复形覆盖、任意次数、任意环和系数模成立，
  特别包含整系数 28.11。交子复形的开邻域与两个开邻域之交相等，三个包含都诱导同调同构，
  原来的子复形包含与开邻域包含的自然性方块严格交换；未引入闭覆盖 MV 的假设或单纯链复形。
  `bettiNumber_union_le` 证明任意域系数下
  `b_(n+1)(K) ≤ b_(n+1)(L) + b_(n+1)(M) + b_n(L∩M)`；
  `bettiOne_union_le` 为有理一阶特例，保留 `b_0(L∩M)` 项，不假设交集连通。
  通用数学归位于 `Homology/Algebra/PushoutHomology.lean`、`Homology/HomotopyEquivalence.lean`、
  `Homology/BettiNumber.lean`、`Homology/SmallChains/{Exactness,BettiBound}.lean`。
  七个相关模块最终各次聚焦检查均 exit=0、零 warning；同调搬运模块最后检查 10.5 秒。
  `.lake/scratch/AuditNightHM2*.lean` 保留 83 项去重后的逐项审计，包括新增 39 项声明及 44 项复用/预审计声明。
  `AuditNightHM2ExactReuse` 首次逐项审计 `pushoutShortComplex`、`pushoutShortExact`、
  `subspaceInclusion`、`twoSetFamily`、`firstSubspaceToSmall`、`secondSubspaceToSmall`、
  两个 `SubspaceToSmall_ι`、`subspaceSmallChainSquare`、`smallChainMap`、`smallChainHomologyIso_hom`；
  `AuditNightHM2BoundReuse` 逐项审计 `finrank_eq_range_add_range`、`homologyBiprodIso`、
  `finiteHomologyType_biprod`、`finiteHomologyType_twoSetSmall`、
  `finiteHomologyType_iff_of_homotopyEquiv`、`finiteHomologyType_geometricSpace`。
  全部闭包只含标准三公理或更少；无 `sorryAx`，不经过 `HurewiczLowDegrees`，未登记根聚合。
  闭曲面顶维同调与 I5 仍属于后续 H-M3/H-M4，不由本次 MV 工具自动推出。

- 2026-09-15（H-M3 低阶同调层，数学提交 `163a27733`）：
  `GeometricHomology` 复用既有有限 simplicial-set realization 的奇异同调桥，证明任意环/系数模的维数以上消失；
  `GeometricConnectivity` 给有限几何复形的局部路径连通与连通到路径连通；
  `BettiPolyhedra` 给低阶 χ 展开、连通图的 `b_1=1-χ` 与 PL 多边形 `b_1=1`。
  `.lake/scratch/AuditNightHM3*.lean` 逐项审计 26 项去重声明（11 新、2 既有复核、13 复用/预审计），仅标准三公理。
  首次复用单独审计：`orderedSimplicialSet`、`orderedSimplicialSet_hasDimensionLT`、
  `geometricRealizationHomeomorphism`、`geometricInclusion`、`DifferentialGeometry.SSet.realizationHomologyIso`、
  `SSet.isZero_homology_of_hasDimensionLT`、`Homology.eulerChar_eq_sum`；另预审计
  `localEuclideanSphereHomologyIso`、`euclideanLocalGenerator_ne_zero`、`euclideanBallLocalGenerator_ne_zero`。
  三条 PL 复用复核为 `IsPLSphere.isCombinatorialManifold`、`IsCombinatorialManifold.card_le`、`IsPLSphere.isConnected`。
  `subcomplexInclusion` 现直接复用原生 `geometricInclusion`，重查 MV 消费者 exit=0。
  五个改动模块均检查 exit=0、零 warning；`BettiPolyhedra` 11.2 秒，MV 消费者 12.1 秒。
  全局 H₂ 的局部检测与跨边符号比较未证明，未声称 H.4a 完成；具体义务和原路线修正在 HANDOFF §8。

- 2026-09-15（H-M4 边界 Euler 与导出邻域层，数学提交 `09bc51619`）：
  `BoundaryEuler.eulerChar_boundaryComplex_eq_two_mul` 对任意有限组合带边 3-流形证明 `χ(∂K)=2χ(K)`；
  `DerivedNeighborhoodHomology` 给导出邻域到原子复形的显式同伦等价，并证明全部 Betti 数与 χ 不变；
  `HandleCount` 给可定向性的导出邻域传递、`χ(∂N(L))=2χ(L)` 与图邻域的 `b₁=1-χ(L)`。
  三模块聚焦检查 exit=0、零 warning；`.lake/scratch/AuditNightHM4{Reuse,Final}.lean`
  逐项审计 32 项去重声明（10 新、22 复用/预审计），全部仅标准三公理。
  首次复用逐项包括 `faceEulerChar_eq_two_mul_of_link_counts`、几何 link/边界面判据、
  `StrongDeformationRetract.toHomotopyEquiv`、`Homology.eulerChar_eq_of_homotopyEquiv`、
  组合流形的 `secondDerived`/`derivedNeighborhood`、`IsOrientable.of_le` 与 `.barycentricSubdivision`。
  I5 未闭合：还需 H-M3 的闭曲面顶维同调、一般 3-流形的 23.19 Betti 不等式，以及 H.4b 的
  `b₁=0 → PL 2-sphere` 识别；未将非球面假设弱化成 `χ≠2`。

- 2026-09-15（H-M5 定向上循环的二重覆盖复形，数学提交 `c6830cc26`、`4e81f6e2d`）：
  第一提交证明有限覆盖复形保持组合流形结构，并以链接的 `IsGlueIso` 传递相干定向；第二提交证明
  `SimplicialBoolCocycle.coveringNeighbor_side`，即提升边两端 sheet 的 XOR 等于基边 `parity`，再把
  `orientationCocycle` 的局部细分定向符号乘以 sheet 符号，构造全局
  `orientationCocycleCoveringOrientation`。最终端点
  `isOrientable_coveringComplex_orientationCocycle` 对任意维有限组合带边流形给出该二重覆盖复形的可定向性。
  `Orientation`、`OrientationCocycle`、`CoveringOrientation` 最终聚焦检查均 exit=0、零 warning，分别为
  32.2、29.3、14.9 秒；`.lake/scratch/AuditNightHM5OrientationCover.lean` 逐项审计 37 项
  （13 项新增/提升端点、24 项复用），全部仅标准三公理。新增/提升端点包括
  `subdivision_carrierFace_spec`、`subdivision_carrierFace_card`、
  `CoherentOrientation.affine_coface_pair_cancel`、两个 `localOrientationSign` 接口、四个局部细分定向符号接口、
  `SimplicialBoolCocycle.coveringNeighbor_side`、`orientationCocycleCoveringOrientation` 与最终可定向性端点；
  关键复用逐项包括重心细分与 carrier、覆盖边提升与面数据、开星局部平凡化、覆盖基顶点的面上单射、
  `CoherentOrientation.changeVertexOrder`、单形边界系数及组合流形余面计数。H-M5 无未闭合端点；
  H-M3/H-M4 的顶维基本类、23.19 与非球面识别缺口保持不变。

- 2026-09-16（H.4b 闭组合曲面球面识别，数学提交 `465433505`）：
  `SurfaceSphereRecognition.lean` 用原始生成树和 Euler 计数产生的对偶余树，将任意连通闭组合
  2-流形分为两个 PL 2-球子复形；共同面的纯 1 维性识别两侧的共同边界，再粘合成 PL 2-球面。
  端点 `IsCombinatorialManifold.isPLSphere_two_of_faceEulerChar_eq_two` 仅假设连通、闭组合 2-流形及
  `faceEulerChar = 2`。聚焦检查 exit=0、零 warning；`AuditHSurfaceSphereRecognition` 审计 33 项（22 新、11 复用），
  全部只含标准三公理。本里程碑首次复用并逐条审计
  `closure_space_sdiff_space_eq_subcomplexGeneratedBy`、
  `inter_closure_sdiff_space_eq_boundaryComplex_of_isCombinatorialManifold`、
  `eq_of_faces_subset_of_space_eq`、`boundaryComplex_boundaryRelSubdivision`、
  `boundaryComplex_full_boundaryRelSubdivision`、`isPLSphere_gluedComplex_of_isPLBall`、
  `isPLHomeomorphOn_gluedMap_of_full`、`exists_face_superset_card_eq_of_isPLBall`、
  `IsCombinatorialManifold.secondDerived`、`secondDerived_isSubdivision`、`exists_primalTree_dualCotree`。
- 2026-09-16（H-M4 / I5，数学提交 `1d7ffe266`）：`BoundaryHomology.lean` 在现有
  `orderedSimplicialSet` normalized chain complex 中构造边界分支定向循环与顶单形边界的联合单射，证明
  `card(other boundary components) ≤ b₂(K)`，并证明连通可定向带非空边界组合 3-流形的奇异 `b₃=0`。
  `faceEulerChar` 的连通分支求和、H.4b 的 `χ=2 → IsPLSphere 2`、`χ(∂K)=2χ(K)` 与 Euler–Betti 展开
  随后给出 `HandleCount.bettiOne_pos_of_boundary_component_not_sphere`，交付 I5；H-M3 的闭曲面全局基本类仍后推。
  三个目标模块聚焦检查 exit=0、零 warning；`fresh.py` 报相对整合分支 7 个改动模块 olean 全部新鲜且零禁用项。
  `.lake/scratch/AuditHI5.lean` 逐项审计 47 个新增声明与 23 个关键复用声明，均只含标准三公理。
  本里程碑首次复用单独审计 `orderedNormalizedChainEquiv`、`orderedNormalizedBoundary`、
  `SSet.finiteDimensional_normalizedChainComplex_X`、`ShortComplex.homologyMapIso`、`isoOfQuasiIsoAt`、
  `LinearMap.finrank_le_finrank_of_injective`、`LinearMap.finrank_range_le`、`LinearMap.ker_eq_bot`、
  `Nat.card_le_card_of_surjective` 与 `Finite.card_option`；并复核 realization/奇异同调桥、分量复形、曲面 Euler 上界、
  H.4b 球面识别、边界定向及边界 Euler 端点的公理闭包。
- 2026-09-16（H-M6 / 22.11，数学提交 `0a4d434c7`）：`FieldPathCones.lean` 将道路锥推广到任意域系数，
  证明单连通空间的一维奇异同调为零；`SurfaceSimplyConnected.lean` 构造闭组合曲面的 ℤ₂ 顶维基本循环，
  得到 `bettiNumber 2 > 0`，再由 Euler–Betti、`χ≤2` 与 H.4b 的 `χ=2 → IsPLSphere 2` 证明
  `IsCombinatorialManifold.isPLSphere_two_of_simplyConnectedSpace`。两个模块聚焦检查 exit=0、零 warning；
  `fresh.py` 报两个改动模块 olean 全部新鲜且零禁用项。`.lake/scratch/AuditHM6.lean` 审计 26 个新增声明与
  18 个关键复用声明，全部只含标准三公理。D4 首次复用逐项审计
  `exists_integralPathTriangle`、`integralPathSimplex`、`integralSimplexPath`、
  `integralPathSimplex_simplexPath`、`orderedNormalizedBoundary_apply_eq_sum_faceCofaces`、
  `orderedNormalizedChainEquiv`、`orderedNormalizedBoundary`、`orderedSimplicialSet_hasDimensionLT`、
  `SSet.isZero_normalizedChainComplex_X_of_hasDimensionLT`、`SSet.finiteDimensional_normalizedChainComplex_X`、
  `ShortComplex.homologyMapIso`、`isoOfQuasiIsoAt`、`SSet.realizationHomologyIso`、
  `geometricRealizationHomeomorphism`、`bettiNumber_zero_of_isConnected`、`eulerChar_eq_sum_bettiNumber`、
  `faceEulerChar_le_two` 与 `isPLSphere_two_of_faceEulerChar_eq_two`。未经过含 `sorry` 的
  `Homology/HurewiczLowDegrees.lean`，也未借用曲面分类。
- 2026-09-16（H-M7 / §21 与 28.20，数学提交 `9bcc38d82`）：`EulerCellOperations.lean` 以
  `OpenCellProfile.Operation` 的 α–δ 四种构造证明开胞腔计数 χ 在单步和有限次细分操作下不变，并将计数桥回
  有限二维复形的 `faceEulerChar`；同时给出按面并集的 Euler 包含排除与沿 PL 多边形粘接的 21.8 加法。
  `SurfaceSplitEuler.lean` 以公共核心、乘积环带、两条多边形边界及切后 PL 同胚定义
  `SurfaceSplitAlongPolygon`，证明 21.10 的 χ 不变；两个互不相交 PL 2-胞腔封口形成
  `SurfaceSplitAndCap`，其 `eulerChar_eq_add_two` 交付 21.11 与 28.20，且结构字段不含 Euler 结论。
  两个模块聚焦检查 exit=0、零 warning；`fresh.py` 报本车道四个改动模块 olean 全部新鲜且零禁用项。
  `.lake/scratch/AuditHM7.lean` 审计 21 个新增声明与 18 个关键复用声明，全部只含标准三公理。
  D4 首次使用或本里程碑复核逐项包括 `faceEulerChar_eq_of_card_le_three`、
  `faceEulerChar_sup_add_faceEulerChar_inf`、`faceEulerChar_bot`、`faceEulerChar_congr`、
  `eulerChar_eq_singular`、`eulerChar_eq_of_isSubdivision`、`eulerChar_union_add_inter`、
  `eulerChar_of_isPLBall`、`eulerChar_of_isPLSphere_one`、`eulerChar_eq_of_isPLHomeomorphOn`、
  `Homology.eulerChar_eq_of_homeomorph`、`Homology.eulerChar_eq_of_homotopyEquiv`、
  `HomotopyEquiv.productConvex`、`Homeomorph.Set.prod`、`IsPLHomeomorphOn.homeomorph`、
  `intersectionComplex`、`unionComplex` 与 `finite_unionComplex_faces`。
- 2026-09-16（H-M8 / 22.5–22.7，数学提交 `3fdf6d58e`）：`SurfaceHomology.lean` 在现有有序
  normalized chain complex 中证明闭连通组合 2-流形可定向时 `b₂=1`、不可定向时 `b₂=0`，再经
  realization/奇异同调桥与 Euler–Betti 展开得到无条件的 22.7。`SurfaceInvariants.lean` 定义标准
  `surfaceHandleCrosscapProfile h m`，对实际给出的标准剖分 refinement 证明 22.5，并导出可定向、一个交叉帽、
  两个交叉帽情形的 22.6 及 `surfaceHandleNumber = h`。这不声称 22.4 的正规形存在性；22.8–22.10 仍待分类。
  两模块聚焦检查 exit=0、零 warning；`fresh.py` 报六个相对整合分支改动模块 olean 全部新鲜、零禁用项。
  `.lake/scratch/AuditHM8.lean` 审计 36 项，全部只含标准三公理。D4 首次使用或本里程碑复核逐项包括
  `orderedNormalizedBoundary_intCast_apply`、`orderedNormalizedBoundary_apply_eq_sum_faceCofaces`、
  `CoherentOrientation.pair_cancel_of_faceCofaces_eq`、`IsCombinatorialManifold.card_faceCofaces_eq_two`、
  `IsCombinatorialManifoldWithBoundary.dualGraph_preconnected`、`SimplicialComplex.orderedNormalizedChainEquiv`、
  `SSet.finiteDimensional_normalizedChainComplex_X`、`SimplicialComplex.orderedSimplicialSet_hasDimensionLT`、
  `SSet.isZero_normalizedChainComplex_X_of_hasDimensionLT`、`ShortComplex.finrank_ker_eq_homology_add_range`、
  `CategoryTheory.ShortComplex.homologyMapIso`、`HomologicalComplex.isoSc'`、`isoOfQuasiIsoAt`、
  `SSet.realizationHomologyIso`、`geometricRealizationHomeomorphism`、
  `eulerChar_eq_one_sub_bettiOne_add_bettiTwo`、`OpenCellProfile.eulerChar_eq_of_isRefinement` 与
  `simplicialOpenCellProfile_eulerChar`。未经过 `Homology/HurewiczLowDegrees.lean`。
- 2026-09-16（H-M9 / B.8 / 26.8，数学提交 `6a02d3559`）：`EuclideanSurfaceOrientation.lean` 证明
  `IsCombinatorialManifold.isOrientable_of_finrank_eq_three` 与 ℝ³ 专门推论。有限连通闭组合曲面先置于大 3-单形内部；
  B.6 的两侧性经子类型拉回后产生一侧闭包的有限带边组合 3-流形，环境仿射定向诱导其边界定向；共同细分将原曲面
  实现为该边界的子复形，限制定向并搬回原三角剖分。全程未使用 `H₃ ≅ ℤ`，没有额外结论型假设。
  聚焦检查 exit=0、10.2 秒、零 warning；`fresh.py` 报七个相对整合基线改动模块 olean 全部新鲜、零禁用项。
  `.lake/scratch/AuditHM9.lean` 审计两个新端点及十四个关键复用声明，均只含标准三公理。逐项复核
  `exists_affineIndependent_openSimplex_superset`、`IsCombinatorialManifold.isTwoSided`、
  `Topology.IsTwoSided.preimage_of_isInducing`、
  `IsCombinatorialManifoldWithBoundary.exists_neighborhood_manifold_pair_of_twoSided`、
  `isOrientable_of_space_subset_convexHull`、`IsOrientable.boundary`、
  `exists_isSubdivision_restrict_isSubdivision`、`isCombinatorialManifold_boundaryComplex`、
  `IsCombinatorialManifold.of_isSubdivision`、`IsOrientable.subdivision`、`IsOrientable.of_le`、
  `IsOrientable.of_isSubdivision`、`frontier_space_eq_boundaryComplex_space_of_finrank` 与
  `isPLBall_convexHull_of_affineIndependent`。
- 2026-09-15（C/L 车道，L.2 接口修正与组合曲面层）：`SphereCase.lean` 的
  `exists_nonsingular_two_cell_of_sphere_boundary` 在 `724267986` 增加实际多面体 3-流形 `M`、
  `B ⊆ polyhedralBoundary 3 M hM`，并在 `hpush` 与结论中都要求 `D₁ '' D₁.domain ⊆ M`；检查 exit=0、
  零 warning，AuditSphereCase 十二项仅标准三公理。`SurfaceNeighborhood.lean`（`cc4e2a06e`）证明导出邻域是带边组合
  2-流形，其边界为有限个两两不交 PL 1-球面，并逐分支取得两个互补 PL 2-球；检查 exit=0、零 warning，
  AuditSurfaceNeighborhood 十二项仅标准三公理。未闭合的是有限 Jordan 边界域的一侧一致性与精确删盘等式，以及任意补盘的
  全局推入；整合后的 `BoundaryPush.lean` 当前只覆盖局部小边界盘。

- 2026-09-15（C.5 桥接，`f1349f5c2`）：`Topology/Algebra/Group/IndexTwo.lean` 构造指标 2 子群的
  `indexTwoHom : G →* Multiplicative (ZMod 2)`，证明满射、核等于原子群，并给出存在指标 2 子群与存在满射到 ℤ₂ 的等价。
  聚焦检查 exit=0、零 warning；AuditIndexTwo 审计 6 个新端点及首次复用的
  `Subgroup.mul_mem_iff_of_index_two`、`Subgroup.index_eq_two_iff_exists_notMem_and`、`Subgroup.index_ker`、
  `MonoidHom.range_eq_top`、`Subgroup.card_top`、`Nat.card_congr`、`Nat.card_zmod`，全部只含标准三公理。
  Bennett 的 `Coefficients`/`CoveringTransfer*` 不含几何单纯链复形、一维 Hurewicz 或次数一 UCT；因此
  `SimplicialBoolCocycle/IsCoboundary ≃ Hom(H₁(K;ℤ),ℤ₂)` 尚未闭合，且未 import 含 `sorry` 的
  `Topology/Homology/HurewiczLowDegrees.lean`。

- 2026-09-15（L.4 条件性骨架，`130e6f402`）：`LoopTheorem/StallingsInduction.lean` 定义
  `NormalSystem.NonsingularCell`、实际二重覆盖及严格降复杂度数据 `DoubleCoverReduction`；
  `simplicialComplexity_lt_of_factorization_of_separated` 由顶点映射因子分解和一个被分开的碰撞对证明严格下降，
  `exists_nonsingular_cell_of_stallings_induction` 按边界球面性和可定向性分支，对复杂度作强归纳并显式消费 Lemma 1、
  Lemma 2、24.7 与 24.8。合并最新整合分支后重查 exit=0、零 warning；AuditStallingsInduction 审计 6 个新声明及
  `mem_vertexCollisionPairs`、`Finset.card_lt_card`、`Finset.ssubset_iff_subset_ne`、`connectedComponentIn`、
  `IsOrientable`、`IsCoveringMap`、`Nat.strong_induction_on`，仅标准三公理。条件性缺口是由 C.4/C.5 与 C.1/C.3
  构造该降阶数据，并完成复杂度相等时限制同胚、基本群满射与指标 2 的矛盾；没有把这些生产者报告为已证。

- 2026-09-16（C.5 闭合，`65bd07eb6`、`cb2153a6c`）：I5 的 `BoundaryHomology`/`HandleCount`
  支撑层推广到任意域，因而直接在 `ZMod 2` 上得到非零一阶同调。`HomologyCocycle.lean` 用
  normalized simplicial chain 与 realization 的奇异同调同构，选取非零同调类的对偶函子并延拓到一链，
  构造真正的非上边界 `SimplicialBoolCocycle`。`DoubleCoverExistence.lean` 的
  `exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere` 将它接到 C.2/C.3，
  无显式 I5 假设地交付连通二重覆盖、有限提升复形及组合带边 3-流形性。两模块聚焦检查
  exit=0、零 warning；`.lake/scratch/AuditC5.lean` 审计 17 项新端点和首次复用声明，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。其中首次复用单独审计
  `DifferentialGeometry.Topology.moduleHomologyClass_surjective`、`moduleHomologyClass_eq_zero_iff`、
  `Module.Projective.exists_dual_ne_zero`、`Subspace.dualLift`、`Subspace.dualLift_of_mem`、
  `Module.nontrivial_of_finrank_pos`、`DifferentialGeometry.SSet.realizationHomologyIso`、`isoOfQuasiIsoAt`、
  `SimplicialComplex.geometricRealizationHomeomorphism`、`orderedNormalizedChainEquiv`、
  `orderedNormalizedBoundary_single_apply`、`simplexBoundaryCoefficient_eq_one_or_neg_one`、
  `ZMod.neg_eq_self_mod_two` 及 C.2/C.3 的连通覆盖端点。未 import、未传递经过含 `sorry` 的
  `Topology/Homology/HurewiczLowDegrees.lean`。L.4 仍需把覆盖复形提升为携带正规系统相容性与严格降复杂度的
  `DoubleCoverReduction`；C.5 的覆盖存在性本身已闭合。

- 2026-09-17（H-M1，H.4a / H.6 当前整合树复核）：`SurfaceHomology.lean` 新增
  `IsCombinatorialManifold.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two`，直接由已证闭连通可定向曲面公式
  `χ=2-b₁` 得到 H.4a 消费端点。`MayerVietorisSubcomplex.lean` 的 28.11 端点
  `exists_mem_inter_of_map_eq_zero` 及 Betti 上界在当前整合树重新确认。两模块聚焦重编 exit=0、零 warning，分别为
  14.4 秒与 10.1 秒；`.lake/scratch/AuditHM1Current.lean` 审计九个新端点、直接生产者与 H.6 端点，全部只含
  `propext`、`Classical.choice`、`Quot.sound`。未 import 或传递经过 `Topology/Homology/HurewiczLowDegrees.lean`。

## 7. 决策与风险

- 2026-09-17（H-M2）：§33 L11–L12 不再以前置 22.8–22.10 的完整曲面分类闭合。Lemma 10 的基本群同构先经独立证明的
  一维 Hurewicz/阿贝尔化桥给 `b₁(Bd X)=b₁(Bd N)`；各 `A'_v` 逐边界封盘后，用 H.4a 的闭可定向曲面公式、Euler
  加法与 H.4b 的 `χ=2` 球面识别证明其为球面删有限开盘。原 Lemma 11 的无分块同胚不进入主链，最终保持
  `A_v ↦ A'_v` 的 PLH 由 Lemma 13 另造。禁止消费含 `sorry` 的 `Topology/Homology/HurewiczLowDegrees.lean`。
- 2026-09-17（H-M3 评估）：`TopologicalCellComplementConnected` 不是现有球面分离链的薄包装。
  `hasTwoComplementComponents_of_isCompact_of_alexanderDualityH0Certificate` 已适用于任意紧致像；真正缺口是任意拓扑
  2-球面的 `HasAlexanderDualityH0Certificate`。现有 `SpecializedAlexanderDuality` 是未生产的条件，且其从两分支反推的
  定理与目标循环；wild sphere 不能用 smooth/open-bicollar，树中无 Čech或紧支撑理论。最窄专门实现估 10k–18k 行，
  完整可复用 Alexander 对偶估 20k–35k；在用户另行批准前暂缓，不把 30.5 报成只差 30.4 的 1k 收尾。
- 2026-09-18（G.5 密度前提，done）：`CapDeletion.lean` 端点 `isPLBall_space_of_isPLSphere_capComplex` 原带的
  `A.space ⊆ closure (A.space \ L.space)` 已有生产者。`ManifoldInteriorDensity.lean` 用树中现成的组合带边流形纯性
  `IsCombinatorialManifoldWithBoundary.exists_face_superset_card_eq` 证明：面基数都 `≤ n` 的子复形（特别是
  `boundaryComplex n K`）在 `K.space` 里的补是稠密的。重述端点
  `isPLBall_space_of_isPLSphere_capComplex_of_isCombinatorialManifoldWithBoundary` 只把密度前提换成
  `IsCombinatorialManifoldWithBoundary 2 A`，无其它新前提：`L` 的基数界由端点已有的 `IsPLSphere 1 L.space` 经
  `card_le_of_isPLSphere` 免费给出。至此 G.5 只剩一维 Hurewicz 桥。
- 2026-09-18（G.5 一维 Hurewicz 桥，评估）：禁止导入的 `HurewiczLowDegrees.lean` 只含二维、三维两条 `sorry`，
  与本题无关，该限制成本为零。方向核对的结论是必须做**难的一半**：Hurewicz 容易一半只给
  `b₁(Bd N) ≤ b₁(Bd X)`，代入 L12 的 `b₁(Bd X) = b₁(Bd N) + ∑v b₁(Â'_v)` 是恒真式；迫使各项为零要
  `b₁(Bd X) ≤ b₁(Bd N)`，即 `H₁(i)` 单，只能经 `ker(π₁→H₁) = 换位子群`。【该条后半段"本库与 Mathlib 均无
  万有系数定理，须从零重做"已于同日撤回，见下一条；HB1–HB6 分解作废。】
- 2026-09-18（G.5 一维 Hurewicz 桥，更正）：**撤回**上一条"无万有系数材料、须在本车道从零实现"的判断。
  搜索范围漏掉了同仓库的兄弟分支 `origin/codex/pc-sorry-free`。该分支有七个本车道完全没有、且无 `sorry` 的文件
  （`UniversalCoefficientsOne` 293、`UniversalCoefficientsOneLinearEquiv` 365、`HurewiczOneAbelianization` 746、
  `HurewiczOneKernel` 453、`HurewiczOnePathLoopBridge` 336、`HurewiczOneVertexPairing` 241、
  `RationalHurewiczOne` 195，合计 2629 行），已用 `git show`／`git grep` 只读核对。
  `tensorRational_abelianizationFundamentalGroup_equiv_of_hurewiczOne` 给出消费端要的
  `ℚ ⊗ Additive (Abelianization (FundamentalGroup X x)) ≃ₗ ℚ ⊗ H₁(X;ℤ)`，条件是可加性、`sphereHurewicz 0` 满、
  核 ⊆ 换位子；容易一半已证，难一半在那边同样未闭合但已收窄到两条具名子事实。
  "难一半不可避免"的结论成立，"须从零实现"的结论不成立。两条限定：ℤ→ℚ 换系数
  （`rationalSingularHomologyOneCoefficientChange`）在那边也只对全不连通空间生产，四个下游端点都把它当显式假设；
  右端是 `ℚ ⊗ H₁(X;ℤ)` 而非本库 `bettiNumber ℚ _ 1` 的对象，接到 `bettiOne` 还要一步 `finrank` 胶水。
  剩余义务改述为：对 `Bd X`、`Bd N`、各 `Â'_v` 生产 `HurewiczOneMultiplicative`、`HurewiczOneKernel`、
  `sphereHurewicz 0` 的满性，加上换系数与 `bettiOne` 收尾。交付路线是**分支收敛**：那七个文件的传递导入闭包有
  163 个文件、约 45600 行不在 Moise 各分支上，不是 cherry-pick，需协调者安排；在本车道重写属重复劳动，不做。
  该分支的 `PiecewiseLinear` 文件数为 0，Alexander 对偶材料与我们同源，故 H-M3 评估不受影响。
  详见 `HANDOFF_CODEX_H.md` 同名更正条目。
- 不采用 Bing 定理 7 的“保留单形”强形式，只用 Moise §8/§35 的紧致图卡归纳（书中 `chap:two-set-gluing` 的方案）。
- 不变域定理不进入 Phase 1（`f(O) = O` 由接口 A 给出，与 Moise 36.1 一致）。
- `PLApproximation`/`PLSmoothing` 以 `Prop` 假设而非 `sorry` 出现：公理审计干净，但**报告时必须说明条件性**。
- 主机内存约 31.5 GB、空闲不足 10 GB：构建限 2 worker；本任务的聚焦检查一次只开一个 `lean.exe`。
- 2026-09-12：Phase 3 按 Moise GTM 47 §30–36（伪胞腔 / 典范构形）而非用户路线图 `main04.tex` 的 Shalen 式章节组织，
  因为本机只有 Moise 的完整书面证明；两者终点陈述相同。Phase 3 的表示层决定 D1–D6（多面体层 + 流形层、不引入带边
  PL 流形图卡范畴、有限复形单纯 ℤ-链、复用 Mathlib/本库覆盖与基本群、只做三种一般位置、外部移植不变域）记录在
  `PHASE3_APPROXIMATION_PLAN.md` §1；最大开放点是同调层（单纯 vs 奇异）。
- Schoenflies 三版本互不蕴含：平面拓扑版（vendored）、PL ℝ³ 版（本链 §17 自证，依赖平面多边形版 3.6、3.3、10.8）、
  光滑 ℝ³ 版（负责人，sorry）。本链不消费光滑版；不重复负责人的工作。

- 2026-09-16（F 车道 S.4 / I1）：`Schoenflies.lean` 已证明原显式 `SchoenfliesInput` 下的
  `isSimplyEmbedded_of_isPLSphere_two` 与 `exists_isPLBall_of_isPLSphere_two`；由有限顶点高度归纳、实际水平盘粘合、
  顶端盘锥和降指标归约完成 17.12。S 的既有 `schoenflies_input` 可直接实例化，不再欠 F 的 I1 生产者。
  五个本次模块检查均 exit=0、零 warning；AuditF246 十八项全部仅标准三公理，fresh.py 为 92/92 fresh。
  证明细节与验证记录见 `HANDOFF_CODEX_F.md` §19.97；F-M5/F-M6 的双点分类和余面异侧义务仍独立待证。

- 2026-09-16（整合，夜）：F 车道交付 17.12，S 车道的 `schoenflies_input` 实例将其消条件，
  `PLSchoenflies.lean` 给出无条件的三维 PL Schoenflies（`IsPLSphere.isSimplyEmbedded`、
  `IsPLSphere.exists_isPLBall_frontier_eq`）。23.9/23.10 与图卡内推移定理的显式 `hSchoenflies`
  参数随之删除，PL 侧不再有该假设。F 车道 92 个模块在合并后的树里逐个重编 exit=0、零 warning，
  250 项命名空间感知审计仅 `propext`、`Classical.choice`、`Quot.sound`；另有一处与既有
  `IsConeBase.of_faces_subset` 的重名已合并为单一声明。
  同夜新增 `MoiseChain.lean` 与 `MOISE_CHAIN.md`：把 `Moise352` 之下的关键路径写成十个具名 `Prop`
  （25.1、25.2、26.4、30.4、30.5、30.6、30.7、33.1、34.1、35.1）与所需词汇，全部通过编译。
  `ThreeCellExtension.lean` 指出计划行 S.7 其实是 P.2 一般定理在 `n = 2` 的实例，已补为具名定理。

- 2026-09-17（F 车道 F5.2 目标区域保持）：`GeneralPositionWithin.lean` 为相对横截和真实双点流形生产者补开目标 MapsTo，
  并在流形自身的度量中实际生产保护奇异盘全像的紧致片与正扰动半径；图卡局部正规化保留指定目标片。
  两模块 exit=0、零 warning，AuditF247 五项仅标准三公理。F5.2 仍 partial；有限图卡 crossing 保持与边界拼装见 HANDOFF §19.98。
- 2026-09-17（F 车道 F5.2 余面分离）：`CofaceSeparation.lean` 从单形内部不交的既有分离生产者，证明指定超平面的两个满维余面对顶点严格异侧，并为满维流形内部面实际选出正、负两侧余面。
  check exit=0、零 warning，AuditF249 五项仅标准三公理。到曲面折叠支的图卡搬运与有限图卡正规化仍待闭合，见 HANDOFF §19.100。
- 2026-09-17（F 车道 F5.2 图卡余面分离）：`CofaceTransport.lean` 从公共细分上的逐面仿射性与载体单射性实际构造像复形，闭合指定超平面的余面严格异侧性在星图卡中的搬运。
  check exit=0、零 warning，AuditF250 两项仅标准三公理。分层约束族的实例化、曲面支归属与有限图卡拼接仍待闭合，见 HANDOFF §19.101。
- 2026-09-17（F 车道 F5.2 分层维数障碍）：`ArrangementConstraints.lean` 已证明原完整仿射无关约束不能容纳全维包络中的四个受迫共平面顶点，故不能直接实例化处理共面双折；检查 exit=0、AuditF251 三项标准三公理。
  F5.2 保持 partial；精确陈述、受影响路线与替代证明方向见 HANDOFF §19.102。按常驻规则转做新 F-M2 非紧多面体接口。
- 2026-09-18（F 车道 26.4 相对子复形细分）：`SubcomplexMesh.lean` 定案 26.4 消费的是限制形细分并打包`exists_isSubdivision_diam_lt_restrict_isSubdivision`；把 MOISE_CHAIN 出路 (a) 的固定形反证为假
  （`not_exists_isSubdivision_faces_subset_forall_diam_lt`）；查出 `Moise264` 结论缺 "Bd Δ 在 M² 中不可缩"。check exit=0、零 warning，AuditF284 三项仅标准三公理；见 HANDOFF_CODEX_F §19.144。
- 2026-09-18（F 车道 F5.2 支跨公共面）：`FoldPlaneCrossing.lean` 把“曲面各支跨越目标公共面”定案为“该支在双点附近于指定平面两侧都有点”，并证明它与该支两个对顶点在该仿射泛函下异号等价；
  由此产出 `IsArrangementGeneralFoldPair` 与共面双折的 `HasPLCrossingAt`。check exit=0、零 warning，AuditF282 共 13 项仅标准三公理。F5.2 仍 partial：这条翻译对两条备选路线中立，
  但两侧性本身仍需由分层通用位置或目标骨架横截各自生产，详见 HANDOFF §19.142。
- 2026-09-17（F 车道新 F-M2 / F6.4）：`LocallyPolyhedral.lean` 交付允许非紧开胞腔的局部多面体谓词、与旧紧致多面体的等价、紧集有限片邻域、正确条件下的闭子集/有限并/交接口及局部有限复形桥接。
  最终 check exit=0、零 warning，AuditF252 共 22 项仅标准三公理。§32 Q.1 可用 `IsLocallyPolyhedral (U \ P)` 陈述非紧部分；未捆绑全局无限三角剖分，范围说明见 HANDOFF §19.103。

- 2026-09-18（30.5 核查，取代 2026-09-17 的 H-M3 评估）：Theorem 30.5 全书只在 §34 Lemma 3 被引用，交来的胞腔是开集上嵌入
  `h` 下多面体胞腔的像，`frontier C₂'` 双领口；双领口情形已由 `TubularExcision.lean:170` + `SphereH1.lean:189` +
  `JordanBrouwer.lean:28` 无条件证出（纯拓扑，已 `#print axioms` 核实）。H-M3 漏查了这一支。决定：以 `Moise305Tame`
  （加 `IsBicollared (frontier C₂)`）替代，估约 1k–2k 行；不实现 wild 球面的 Alexander 对偶。详见 `MOISE_CHAIN.md` 同名条目。

### Half-prism acceptance update (2026-09-19 UTC)

E3 1cea2fbe7 is independently accepted: the supplied compatible PLPieceIn chart
produces the half-prism ball, its disjoint endpoint disks, exact safe frontier
and path connectedness. All three declarations, seven critical reuse entries,
an actual nonempty Euclidean box model and 13 applicable linters pass. The
original Delta/D1/D2-to-compatible-chart construction is still E3's active gap.
F ec3b6b063 strict descent and 52ead09cc finite-cover realization are now
independently accepted; h 97d4a948d derived-neighborhood corrections remain
queued. h continues the same lane
by testing and proving the global regular-neighborhood meaning of its tower.

### Cover realization and descent update (2026-09-19 UTC)

F through 52ead09cc is independently accepted: four modules, 12 new
nonautomatic declarations, ten critical reuse entries, two concrete models
and all applicable lint checks. Equality of complexity now constructs a PL
section on the image, extends it across the proved neighborhood deformation
retraction by homotopy lifting, and contradicts connected double-covering.
Thus strict descent is proved from the existing full connected cover diagram.
The new finite-cover producer constructs the global PL projection with exact
projection and fiber equations and preserves manifold structure/connectedness.

The remaining lift construction must still produce a complete nonempty
NormalSystem and its boundary-compatible smaller neighborhood. In particular,
the fixed relativeDerivedNeighborhood carrier equation has an independently
verified missing-point obstruction under explicit fixed-edge/coface hypotheses.
The actual compatible-triangulation repair is next;
no universal impossibility theorem for every NormalSystem is claimed. The concrete simplex-times-Bool model tests finite-cover realization,
not a connected DoubleCoverDiagram. E3 ace162dcd disk-neighborhood production
is newly queued and E3 continues simultaneous subdivisions and actual traces.


### M304 surface-region complement checkpoint (2026-09-19 UTC)

`CircleArcComplement.lean` and `SurfaceSubcomplexComplement.lean` construct
actual complementary arcs and finite surface-region complements with the exact
boundary carrier. Three new declarations, two retained ClosedCover declarations,
nine critical reused entries and three models pass the standard-axiom and
13-linter audit with zero diagnostics. Frozen evidence is in
`moise304-reading/surface-complement-checkpoint/`. The connected annulus core
and nonseparating-circle caps are still in progress; full 30.4 remains open.


### M304 nonseparating annulus complement checkpoint (2026-09-19 UTC)

`SurfaceAnnulusComplement.lean` constructs a finite connected orientable
surface with boundary as the exact closed complement of an arbitrarily small
PL annulus around a nonseparating circle. It retains the actual bicollar and
both disjoint endpoint circles, and proves the Euler characteristic is
unchanged. Twelve declarations (nine new), twelve critical reused entries,
three models and all 13 applicable linters pass with standard axioms and zero
diagnostics. Frozen evidence is under
`moise304-reading/annulus-complement-checkpoint/`. Disjoint cap attachment,
ambient separation preservation and full 30.4 remain open.


### M304 disjoint caps and exact Betti descent (2026-09-19 UTC)

Actual disjoint disk caps now construct the finite closed connected surface
and prove its Euler characteristic increases by two. `AnnulusCapping.lean`
combines this with an actual annulus decomposition in ambient dimension three
to prove `bettiOne result + 2 = bettiOne source`. The five changed modules,
15 declarations (ten new), ten critical reused entries, four geometric models,
four explicit instances and all 13 applicable linters pass with standard
axioms and zero final diagnostics. Frozen evidence is under
`moise304-reading/annulus-capping-checkpoint/`. The input caps are actual
disjoint disks with exact boundary and intersection equations; their geometric
production and preservation of ambient separation remain E3 work. No full
30.4 completion is claimed.


### M304 common spanning-disk and annulus witnesses (2026-09-19 UTC)

`SpanningDiskAnnulus.lean` produces the annulus, finite orientable complement
and enlarged spanning disks together, with common endpoint boundary circles,
exact intersections, unchanged Euler characteristic, carrier-cover equations
and the relative-neighborhood data for E3. It covers separating and
nonseparating circles and derives connectedness in the latter case. Six
native declarations, ten reused entries, three geometric models, one retained
conditional consumer, two instances and 13 linters pass with standard axioms
and zero diagnostics. All three older public signatures are unchanged.
Frozen evidence is under `moise304-reading/spanning-disk-annulus-checkpoint/`.
The enlarged disks still share the original disk; disjoint caps and full 30.4
are not claimed.

### M304 components and endpoint circles (2026-09-19 UTC)

`AnnulusComponents.lean` produces the two finite connected disjoint surface
components of a separating annulus complement and assigns their complete
boundaries to the given negative and positive endpoint circles. General
closed-cover and bicollar component formulas, plus boundary restriction to a
component in every dimension, supply the proof. Four changed modules and four
existing consumers pass focused compilation. The audit checks 28 native
declarations, 12 reused entries, six actual models, one conditional consumer,
three instances and 13 linters with standard axioms and zero diagnostics.
Frozen evidence is under `moise304-reading/annulus-components-checkpoint/`.
The cube model verifies both actual components and their exact boundary
circles. Disjoint cap production, ambient separation and full 30.4 remain open.

### M304 separating annulus caps and Betti descent (2026-09-19 UTC)

`SurfaceBoundaryCapping.lean` constructs actual disjoint closed caps of two
disjoint connected surface components. `AnnulusCapping.lean` now derives two
finite connected orientable nonspherical closed surfaces from a separating
essential circle and supplied disjoint disk caps. Their first Betti numbers
sum to the source first Betti number and each is strictly smaller. The two
module checks and the audit of five native declarations, 13 reused entries,
three geometric models, four instances and 13 linters pass with standard
axioms and zero diagnostics. The new actual model gives two disjoint cube
boundaries with Euler two and first Betti zero. Frozen evidence is under
`moise304-reading/separating-annulus-capping-checkpoint/`. Cap production,
ambient separation transfer and full 30.4 remain open.

### M304 smaller separating surface after capping (2026-09-19 UTC)

`SurfaceCompression.lean` combines both annulus-complement cases into a
proved compression step. Actual disjoint caps and separation by their union
produce a finite connected orientable two-sided closed separator contained
in that union, with strictly smaller first Betti number. The separating case
uses the actual capped pair and Phragmen-Brouwer. Both native declarations,
ten reused entries, three concrete probes and 13 linters pass with standard
axioms and zero diagnostics. Frozen evidence is under
`moise304-reading/surface-compression-checkpoint/`. Essential disk production,
disjoint cap geometry and separation of the capped union are still upstream
obligations; full 30.4 is not claimed.

### M304 actual minimal Betti separators (2026-09-19 UTC)

The general compact-set separator construction now produces an actual
finite connected closed separator of minimal first Betti number in the
specified open region. The spherical-shell specialization lies in the shell
interior and is minimal among all finite connected closed separators of its
two boundary components. Both changed modules and two existing consumers
compile without diagnostics; the audit checks 19 native declarations,
11 reused entries, five concrete models and 13 linters with standard axioms.
A cube comparison proves a produced two-point separator has Betti zero and
is a PL sphere. Frozen evidence is under
`moise304-reading/minimal-separator-checkpoint/`. The general shell minimizer
is not yet proved spherical; the essential disk and separation-preserving
disjoint cap producers are still needed for full 30.4.


### M304 essential singular disk production (2026-09-19 UTC)

From a finite connected nonspherical closed surface inside an open simply
connected U, the new SurfaceCompression producer constructs an actual PL
singular disk with a planar PL two-ball domain and an actual finite WB3
neighborhood N contained in U. Both the entire surface and disk image lie
in the same N interior. Exact boundary equations and a free homotopy to
the original nontrivial loop retain non-nullhomotopy on the surface; that
original class is also proved trivial in the same N. Reusable open-target
relative approximation, arbitrary planar PL disk extension, and free-loop
filling are separate native leaves. Five changed/new sources and one
unchanged key dependency compile without diagnostics. The audit covers
11 native declarations, 13 reused entries, two nondegenerate geometric
models with four supporting declarations, and all 13 applicable linters;
all axiom closures are standard. Frozen evidence is under
`moise304-reading/essential-singular-disk-checkpoint/`. This is singular disk
production only: embedded disks from 26.4, physical disjoint caps and ambient
separation are still needed for full 30.4. Root builds remain stopped.


### M304 embedded positive-genus compression (2026-09-19 UTC)

The premise-free native `exists_embedded_torus_compression` constructs an
actual finite embedded torus K in Euclidean three-space, a nonseparating
essential PL circle C, its PL annular neighborhood W, and the same connected
complement R = closure(K minus W). A fixed standard triangle circle is first
thickened to a finite embedded solid torus; the untwisted disk cylindrical
diagram supplies all subsequent objects. A middle cross-section is an actual
embedded spanning disk with intersection K exactly C. Two other cross-sections
are actual nonempty disjoint PL cap disks. Their intersections with both K
and R equal exactly their prescribed boundary circles, which are the two
ends of W. Native annulus capping gives an actual PL sphere P with first Betti
number zero; the same chain proves first Betti number two for K and strict
descent. The product homeomorphism and non-nullhomotopy of C are independently
retained in the statement, as is connectedness of K minus C.

Seven new natural-topic leaves are registered in the flat root aggregate.
AnnulusComplement now reuses the extracted annulus boundary/triangulation API;
its public signature is unchanged. All eight new/changed sources and three
existing consumers compile without diagnostics. The complete audit covers
12 native declarations, 18 critical reused entries and three concrete
nondegeneracy certificates, with all 13 applicable linters and only standard
foundational axioms. The native reachable import graph has 561 modules and
1110 edges without cycles. Eleven source/object/receipt sets, the passing
audit and raw/normalized hashes are frozen under
`moise304-reading/torus-compression-checkpoint/`.

This closes a genuine positive-genus nonempty compression instance, including
the geometric disk/cap producers for this torus. It does not supply arbitrary
30.4 surfaces with disjoint caps or prescribed ambient separator targets.
The unrestricted embedded-disk producer and general separation-preserving
compression remain upstream obligations. Root builds remain stopped; shared
E outputs and other lanes' source files were not changed.


### M304 full frontier of a disk cylindrical diagram (2026-09-19 UTC)

`IsCylindricalDiagram.image_side_eq_boundaryComplex` and
`IsCylindricalDiagram.frontier_eq_image_side` identify the entire boundary
of a finite embedded three-manifold carried by a disk cylindrical diagram
with the actual cylindrical side image. No pointwise untwisted-end hypothesis
is needed. Interior strip charts first put any remaining frontier in the
bottom disk. The native closed-surface complement producer would turn an
extra boundary component into a nonempty closed surface inside that disk;
the new general `IsCombinatorialManifold.not_subset_of_isPLBall` excludes
this by invariance of domain. It applies in every positive dimension.

Both new leaves are registered in the flat root. Their final source bytes
compile with zero diagnostics. The audit checks all four native declarations,
nine critical reused declarations and an actual triangle solid-torus example
with nonempty interior and exact full frontier, all with only standard
foundational axioms. All 13 applicable linters pass. The reachable native
import graph has 477 modules and 919 edges and is acyclic. Sources, objects,
receipts, audit and raw/normalized hashes are frozen at
`moise304-reading/cylindrical-frontier-checkpoint/`.

This supplies the missing ambient-boundary identity for the concrete torus
compression. Common actual separator targets are the next obligation; this
checkpoint does not assert general separation-preserving compression or
close Moise 30.4. Root builds remain stopped and shared E outputs are unchanged.


### M304 common actual targets for torus compression (2026-09-19 UTC)

The premise-free native `exists_embedded_torus_compression_separating_points`
retains the same embedded torus, essential nonseparating circle, annulus,
connected complementary annulus, proper spanning disk, exact disjoint caps,
and first-Betti descent from two to zero. It additionally returns the actual
finite solid torus N and identifies the original surface with frontier N.
The capped sphere is exactly the frontier of the remaining embedded disk
prism, an actual three-ball B. It produces q in interior B and z outside N,
proves q and z distinct, and proves that both surfaces separate {q} and {z}.
The original `exists_embedded_torus_compression` keeps its exact public
signature and is now a corollary of this stronger producer.

`IsPLHomeomorphOn.frontier_prism_image` gives the general ambient-frontier
identity for embedded disk prisms. The new cylindrical separation API works
for any targets H contained in the remaining ball interior and K contained
in the full three-manifold exterior. It derives both separations from the
actual frontier identities; neither separation is assumed.

All three new/changed modules compile without diagnostics, and both new
leaves are registered in the flat root. The complete audit checks five native
declarations, 25 critical reused declarations and five external certificates,
with all 13 applicable linters and only standard foundational axioms. The
certificates recheck the original nonempty disjoint caps and essential proper
disk, then certify common nonempty open regions and two actual disjoint PL
three-ball targets with nonempty interiors for the same torus/sphere pair.
The two-ball certificate is external audit evidence, not a separate native
public theorem. The reachable native import graph has 565 modules and 1118
edges, with no cycles. Three source/object/receipt sets, the audit, census and
raw/normalized hashes are frozen at `moise304-reading/torus-separation-checkpoint/`.

This closes the concrete positive-genus compression instance through actual
preserved separation. It does not produce embedded splitting disks or safe
replacement neighborhoods for arbitrary surfaces in Moise 30.4. Those general
26.4/30.3 obligations remain in their existing lanes. Root builds remain
stopped; shared E outputs and other lanes' source files were not changed.


### M304 native three-ball target production (2026-09-19 UTC)

`IsCylindricalDiagram.exists_separating_ball_pair` now constructs actual
PL three-ball targets for any disk cylindrical diagram carrying a finite
three-manifold in an ambient real normed space of dimension three. Their
interiors are nonempty, they are disjoint, the first lies inside the remaining
prism interior, and the second lies outside the full three-manifold. Both
the original side and the capped side separate these targets. The target
locations, nonemptiness and separations are produced, not assumed.

The premise-free native `exists_embedded_torus_compression_separating_balls`
retains every essential-circle, annulus, complement, proper disk, exact-cap
and Betti field of the original torus compression, and adds these same actual
ball targets with their locations and both separations. The original and
point-target theorem signatures are unchanged. The three-ball witness is
therefore no longer confined to external audit evidence.

Both changed modules compile without diagnostics. The complete audit covers
seven native declarations, 26 critical reuses and six concrete certificates,
including a certificate coupling the same essential circle and proper disk
to the native ball targets and first-Betti descent from two to zero. All 13
applicable linters pass and all axiom closures contain only standard
foundational axioms. The reachable import graph remains acyclic, with 565
native modules and 1119 edges. Three source/object/receipt sets and the audit
are frozen at `moise304-reading/torus-ball-targets-checkpoint/` with raw and
normalized source hashes. Root builds remain stopped and shared E outputs
are unchanged. General 26.4/30.3 and arbitrary-shell 30.4 remain open gates.


### M304 positive-genus compression in an actual spherical shell (2026-09-19 UTC)

The premise-free `exists_embedded_torus_compression_in_spherical_shell`
retains every original same-object torus, essential nonseparating circle,
annulus, complement, proper spanning disk, exact disjoint caps and first-Betti
2-to-0 field. It constructs a positive-width distance-band spherical shell.
The torus, capped PL sphere, entire left compression three-ball and middle
spanning disk lie in this shell's interior. Both surfaces separate the shell's
actual inner and outer metric boundary spheres.

The general `exists_isSphericalShell_separating_frontiers` only assumes a
compact outer set N, a subset B of N and a nonempty interior of B. It constructs
a round shell containing N minus interior B and both frontiers in its interior,
and proves that both frontiers separate the shell boundary spheres. B need
not be closed. Spherical shells are also transported through embeddings, and
the standard norm-band example is extended to distance bands about any center.
All earlier SphericalShell declarations are retained unchanged; TorusShell is
registered in the flat root.

The new combined import first exposed a stale inherited MoiseChain object that
still defined IsTopologicalSolidTorus internally. Current source already
imports the canonical SolidTorus definition. A readonly private refresh of
MoiseChain resolved the collision; SphericalShell, TorusShell and the existing
TameNestedCells consumer then compiled with zero diagnostics. Neither readonly
source nor any MoiseChain contract was edited, and shared E outputs remain
unchanged.

The final audit covers all 20 native declarations in the two changed/new
leaves, 31 critical reuses and nine concrete certificates, with all 13 applicable
linters and only standard foundational axioms. The certificates keep the same
essential disk inside the actual shell, check an open inner set for the general
frontier producer, and instantiate the existing Betti-minimal separator producer
on this shell: its first Betti number is zero and native sphere recognition
proves it is a PL sphere. The reachable native graph has 618 modules and 1236
edges and is acyclic. Four source/object/receipt sets, including the two readonly
refreshes, are frozen with audit and raw/normalized hashes at
`moise304-reading/torus-shell-checkpoint/`.

This is a concrete positive-genus instance with an actual Moise304 shell input.
It does not prove Moise304 for an arbitrary supplied shell. General embedded-disk
and safe replacement-neighborhood producers remain upstream gates. Root builds
remain stopped as instructed.

### M304 embedded meridian and nontrivial boundary kernel (2026-09-19 UTC)

The premise-free `exists_embedded_solid_torus_meridian` projects the same
embedded solid torus, quarter-height circle and spanning disk from the actual
torus-compression producer. It retains the exact disk-boundary parametrization,
frontier intersection, connected boundary complement and first Betti number two.
The disk minus its boundary lies in the solid torus interior and is nonempty.
The same circle inclusion is not nullhomotopic in the torus boundary, but is
nullhomotopic inside the solid torus through that embedded disk. A loop on this
circle has nontrivial image in the boundary fundamental group and trivial image
in the solid torus fundamental group.

The general `fundamentalGroup_map_eq_one_of_nullhomotopic` belongs in
Topology/FundamentalGroup/Nullhomotopy. It works for arbitrary topological spaces
and every basepoint, without connectivity or separation hypotheses. It uses the
existing free-to-based nullhomotopy equivalence; no new contraction assumptions
are introduced into the concrete meridian producer. Both new leaves are in the
flat root aggregate.

Both modules compile with zero diagnostics. All two native declarations, eight
critical reuses and three independent certificates have only standard
foundational axioms. All 13 applicable linters pass. The certificates preserve
the same nonempty proper disk and circle, derive a genuinely nontrivial kernel
and noninjective boundary inclusion, and check that the generic nullhomotopy
lemma does not need connectivity. The native import graph is acyclic with 571
modules and 1128 edges. Two complete source/object/receipt sets and the audit
are frozen at `moise304-reading/torus-meridian-checkpoint/` with raw and normalized
source hashes. Root builds remain stopped; shared E outputs are unchanged.
This is an actual solid-torus instance, not a general embedded-disk producer for
arbitrary three-manifolds or a proof of arbitrary-shell Moise304.

### M304 essential meridians at every cylinder height (2026-09-19 UTC)

`IsCylindricalDiagram.exists_essential_slice_disk` is a generic producer for
finite embedded cylindrical three-manifolds with a PL disk as cross-section and
pointwise identified ends. For every t in the closed interval [0,1], it supplies
an actual parametrized slice disk, its exact boundary circle and exact ambient
frontier trace. The disk minus its boundary is nonempty and lies in the ambient
manifold interior. The boundary circle is nonseparating and not nullhomotopic in
the manifold frontier, but is nullhomotopic inside the same manifold through
that slice disk. No torus or compression conclusion is assumed.

`IsCylindricalDiagram.isConnected_sdiff_slice` now accepts the closed interval,
including the glued end slices. Its assumptions still require neither untwisted
ends nor a finite-dimensional target. The original two other CylindricalCircle
signatures are unchanged. CylindricalFrontier and all three existing torus
consumers were privately rebuilt after this deliberate hypothesis weakening.
The new CylindricalMeridian leaf is registered in the flat root.

Six modules compile without diagnostics. The audit covers all four native
declarations in the two changed/new leaves, 12 critical reuses and two actual
model certificates. The first constructs one embedded solid torus and validates
all its slice disks simultaneously. The second checks both glued ends, their
nonempty disk interiors and disjointness from the middle disk. All 13 applicable
linters pass and every axiom closure uses only standard foundational axioms.
The reachable native graph is acyclic with 479 modules and 922 edges. Six complete
source/object/receipt sets and the audit are frozen with raw and normalized
source hashes at `moise304-reading/cylindrical-meridian-checkpoint/`.
Root builds remain stopped and shared E outputs remain untouched. Arbitrary-shell
Moise304 and a general embedded-disk producer remain separate open gates.

### M304 boundary-only endpoint data and general cylindrical compression (2026-09-19 UTC)

`IsCylindricalDiagram.image_subcylinder_inter_slice` now requires only equality
of the two endpoint images of the subcylinder. Its conclusion no longer assumes
pointwise endpoint agreement on the entire cylinder cross-section. The proof
uses endpoint injectivity and the actual invariant endpoint sets. It still
requires no finite-dimensional source or target. Its former CylindricalProduct
import has been removed.

This removes the endpoint agreement hypothesis entirely from the capping
producer. Its canonical name is now `IsCylindricalDiagram.exists_capped_surface`,
replacing `exists_capped_surface_of_eq_ends`. For any embedded PL disk cylindrical
diagram in a three-dimensional real normed space, the same actual annulus,
complement and two disjoint caps produce a PL sphere, with exact cap traces and
first Betti numbers two and zero. No pointwise endpoint agreement is assumed.
All existing Lean callers have been updated; the three TorusCompression public
statements remain exactly unchanged.

The essential-slice-disk producer now requires pointwise endpoint agreement
only on the disk boundary circle. The interior of the cross-section is no longer
constrained by that additional equation. All closed-interval heights, exact
proper disk traces and both nullhomotopy conclusions are retained.

Seven affected modules and the final external audit compile without diagnostics.
All eight native declarations in the four changed leaves, 12 critical reuses
and two actual all-height/glued-end model certificates have only standard
foundational axioms. All 13 applicable linters pass. The native import graph is
acyclic with 566 modules and 1120 edges. Seven source/object/receipt sets and the
complete audit are frozen with raw and normalized source hashes at
`moise304-reading/cylindrical-boundary-checkpoint/`. No root build or shared E
output write was performed. Arbitrary-shell Moise304 and the remaining upstream
embedded-disk and replacement-neighborhood producers are not claimed complete.
### Compact smoothing: cap comparison and actual graph handles accepted

S 4627710d3 and 3c08c2aba passed independent integration replay: seven fresh
modules, all 27 nonautomatic declarations, 34 distinct critical reused names,
two concrete geometric scenarios with six probe declarations, and 13 applicable
linters. All axiom sets are standard and all checks contain zero diagnostics.
The nontrivial sphere-cap reparametrization fixes the lower ball and moves an
interior cap point; the tetrahedron model produces four vertex balls and an
actual loop-closing edge handle attached in the intrinsic boundary of the old
neighborhood, with the target equal to the next graph neighborhood.
These are genuine zero/one-handle producers and topological cap comparisons.
Two/three-handle product pairs, finite global assembly, smooth attachments and
framings, corner rounding and the smooth two-sphere input remain open. S is
already continuing the triangle two-handle layer. No smooth radial extension
at the center or completed compact smoothing theorem is claimed.


### Source review: actual producers and conditional gluing

F's two real compatible-neighborhood construction modules through 8728c1b09
are independently accepted: 18 declarations, nine key reused declarations,
two nonempty models and 13 clean linters, only standard axioms. The old fixed
NormalSystem formula is being replaced; consumer migration is not yet accepted.
h's a598916fd glues supplied compatible stage SDRs and produces the finite
constant case, but the nonconstant geometric system and its relation to the
book's single locally finite derived triangulation remain open. h continued
that real producer at its completed-round boundary. E3's ace162dcd is held
because its 1206-line disk module duplicates 917 lines of canonical
FreeTriangleNeighborhood; a generalization with boundary corollary is due at
the next delivery, without interrupting the current geometric proof.

## Autonomous-window final acceptance (2026-09-19)

The final source checkpoint is 752c572ae822e48b99c3dbd00a8f6a0faaa439be. The morning report records 41 independent acceptances, the exact net Lean delta, pending F/E3/M304 source, and the remaining mathematical gates. No new proof rounds are assigned after 14:19 UTC. Full-root compilation remains unclaimed. See MORNING_ACCEPTANCE_20260919.md for the governing final snapshot; earlier active-round rows are historical.


## Owner-authorized resumption after the overnight cutoff

At 2026-09-19T14:32:35.604282+00:00 the owner explicitly requested checking tools and continuing work.
The tools and Lean 4.33.1 are available. The previous twelve-hour window and
its morning report remain closed historical records. This new stage resumes
the same five tasks, one mathematical lane each, with hourly quiet follow-up
and no newly inferred deadline. Existing compiler leases are renewed under
the same two-private-checker and three-total-Lean limits. The h lane may now
place its general helper in Topology/LocallyFiniteSeparation.

First independently replay M304 734c87b5f, E3 5877584aa and F f0482b620 beyond
the accepted frontiers. Continue actual geometric producers at their recorded
gaps; no new tasks/subagents, no routine mid-round status requests and no
automatic full-root rebuild. New-stage receipts live in
.lake/resumed-stage-20260919.json; the prior morning accounting is preserved.

### M304 prescribed-shell common annular neighborhood (2026-09-19 UTC)

The canonical common-circle construction now covers arbitrary finite orientable
surfaces with boundary, preserving both old sphere-only signatures as consumers.
The same common derived neighborhood is constructed as a finite WB3 solid torus
inside any prescribed open U, with actual annular traces on both supplied surfaces.
For an actual spanning disk, it avoids a prescribed closed forbidden set and
leaves a proved nonempty part of the disk outside the neighborhood. The spherical
shell specialization retains the given shell and its original inner/outer
boundary targets and constructs the neighborhood in that shell's interior.

All 19 declarations in the three changed/new and two unchanged dependency leaves,
18 critical reuses, two actual essential-torus-disk certificates and 13 linters
pass with standard axioms and zero diagnostics. The older nested sphere consumer
and its trivalent graph model also compile unchanged. Fourteen private module
checks and the complete audit are frozen at
`moise304-reading/common-spanning-checkpoint/`; the native reachable graph has
600 modules and 1201 edges without cycles. No full-root verification is claimed.

The annuli are not yet marked by the original surface bicollar or aligned with
the splitting-prism endpoints. E3 retains that interface. The input embedded
disk is supplied; no general embedded-disk producer, disjoint caps, or proof
that a capped union separates the original targets is inferred. Arbitrary-shell
Moise 30.4 remains open. See `HANDOFF_CODEX_M304.md` for the exact native APIs,
integration provenance, concrete nondegeneracy evidence and remaining gates.

### M304 local separation transfer along the original disk (2026-09-19 UTC)

The supplied common annular neighborhood now feeds the actual enlarged-disk
and splitting-ball producers. `SpanningDiskSeparation` constructs a finite
PL ball B in the prescribed open region and a finite polyhedral separator
P = closure(S minus B) union frontier B. It proves original-disk containment
in frontier B, exact original-surface traces in B, agreement with S outside
B, separation of the original targets, and a nonempty added part. The shell
version constructs the common solid torus and retains the original X,B0,B1;
the full disk's containment in interior X is an explicit geometric input.

The general producer only assumes a compact relative neighborhood A; the
common-annular case is its corollary. The two mathematical modules contribute
four new declarations. All 15 declarations in those modules, 18 critical reuses,
two actual essential-disk
models and 13 linters pass with standard axioms and zero diagnostics.
Thirteen private module checks and the complete audit are frozen at
`moise304-reading/spanning-separation-final-checkpoint/`. The native graph has
848 modules and 1789 edges without cycles. No full-root build is claimed.

P is not asserted to be a closed surface. The local boundary disks M,Q meet
on a proved nonempty circle, so they are not the required disjoint final caps.
The accepted integration capping/realization interfaces were inspected and
remain the canonical consumers after E3's original-boundary marking is
available. A separation proof for that actual capped surface and a general
embedded essential-disk producer remain open; arbitrary-shell 30.4 is not
marked complete.

### M304 separation of a genuine capped surface (2026-09-19 UTC)

`SurfaceCappingSeparation` now proves separation of the literal retained
surface union two end disks, given an actual PL compression ball N with
S intersect N = W and frontier N = W union D0 union D1. The shell theorem
retains the original X,B0,B1, proves containment in interior X and agreement
with S outside N, and proves separation of those same original targets.
Separation of the final union is not an input.

The proof derives the needed one-sided local behavior from the native PL
surface neighborhood and complement-component theorems. It constructs
U minus N on one original side and proves its frontier lies in the actual
capped union. Its generic topological calculation and its regular-closed
region version are reusable beyond the PL ball corollary. This does not use
separation of the previous, larger polyhedral P to infer separation of the
smaller final surface.

All 18 declarations in five mathematical modules, 16 critical reuses, an
actual essential-torus compression in its original shell, and 13 linters
pass with standard axioms and zero diagnostics. The test discards the
model's previous post-capping separation and proves it again by the new
transport theorem, retaining nonempty targets, disjoint disks, Betti numbers
2 and 0, the proper essential spanning disk, and the exact prism traces.
Thirteen private module checks include the eight direct dependents. The
native graph has 545 modules and 1085 edges without cycles. No full-root
build is claimed. See `HANDOFF_CODEX_M304.md` for proof and receipt details.

The remaining arbitrary-shell 30.4 gates are production of the embedded
essential disk and alignment of the original surface with the actual
compression wall/end circles. Separation transport is now proved once those
geometric inputs exist; the accepted capping/realization APIs still provide
the canonical closed-manifold realization. No E3 geometric file is changed.

### M304 connected separating component and strict Betti descent (2026-09-19 UTC)

`SurfaceCompressionSeparation` now constructs the finite connected closed
surface P from an original separator S, an essential circle with centered
annulus, and actual PL compression-ball/disjoint-cap geometry. It constructs
the retained WB2 surface R, derives the annular neighborhood and cap traces,
proves separation of the cap union, and selects an actual connected component
P that still separates the original targets and has strictly smaller first
Betti number. The original-shell version retains X,B0,B1 and proves P lies
in interior X. No result manifold, final separation or Betti decrease is an
input to these new producers.

Both essential-circle cases use the pre-existing native capping chain.
The nonseparating case decreases beta by two. In the separating case the
original essential circle, the actual half-annulus cylinder and spherical
disk-complement theorem prove that neither capped component is a sphere;
their positive Betti numbers sum to the original one. Phragmen-Brouwer
selects a component preserving separation. The former `SurfaceCompression`
consumer retains its public signature and now follows the stronger component
theorem. The actual torus test discards its old final separation and invokes
the new original-shell producer, verifies the produced component equals the
literal capped sphere, and retains source/result beta 2/0 and the original
proper essential disk, caps and nonempty targets.

The critical `SphericalDiskComplement` receives only coordinator-authorized
line wrapping and its required header. The physical capping proofs remain
canonical native reuses. See `HANDOFF_CODEX_M304.md` for exact theorem names,
proof mechanisms, model scope and verification receipts. General production
of an embedded essential disk and E3's actual original-wall/cap marking
remain open; unrestricted arbitrary-shell Moise 30.4 is not complete.

All 14 declarations in the three changed/new mathematical modules, 26
critical reuses, the actual torus model and 13 applicable linters pass with
standard axioms and zero diagnostics. The new leaf is registered in the
flat root; ten former public signatures are unchanged. The reachable native
graph has 605 modules and 1216 edges without cycles. Fourteen source-matching
module receipt sets and the final audit are frozen at
`moise304-reading/compression-separation-checkpoint/`. No full-root build or
independent integration acceptance is claimed.

### M304 finite surface cuts and side kernels (2026-09-19 UTC)

`SurfaceCutting` now constructs actual finite connected WB3 cut complexes
A,B for an original connected finite K and connected separating interior
surface L. It proves A union B = K, A intersect B = L, exact boundaries
including the old boundary pieces, and actual boundary-component labels
whose spaces equal L. In real ambient dimension three it derives separation
and orientability of the cut pieces. Its separate collar producer retains
the literal inclusion into the original K and the supplied relative
neighborhood.

`FundamentalGroup/OpenCoverKernel` proves that a nontrivial overlap element
killed in the original ambient space forces a nontrivial kernel into one
of the two members of an actual open path-connected cover. The proof uses
native van Kampen and injectivity in an amalgamated product. The
`BicollarKernel` specialization constructs such a side kernel when the
original ambient space is simply connected and the compact connected
collared surface is not. It does not assume the desired side kernel.

The actual model keeps one finite PL ball K and its embedded beta-two
torus L throughout: it obtains the actual orientable cut manifolds and
boundary components, a nontrivial pi1(L)-to-pi1(K) kernel, and an open-side
kernel from a collar contained in interior K. Transport from those open
sides to the finite cut manifolds and their boundary inclusions remains
unproved. General Moise252-to-Moise264, including the full component,
nonseparating and ambient hypotheses, is still open. No embedded essential
disk or arbitrary singular-disk normalization is claimed; F and E3 retain
their proof and compression-geometry lanes.

The eight native declarations, 27 critical reuses, one actual model with
four private helpers and 13 linters pass the axiom audit with standard
foundational axioms and zero diagnostics. The three new leaves are registered
in the flat root. Their native graph has 508 modules and 989 edges without
cycles or HurewiczLowDegrees. All existing mathematical sources are
unchanged. See HANDOFF_CODEX_M304.md for exact APIs, proof mechanisms and
frozen receipts. No full-root build or independent acceptance is claimed.

Nine source-matching private module receipt sets and the final audit are
frozen at `moise304-reading/surface-cutting-checkpoint/`, manifest SHA256
`2B430531079C51AF7D64907068EC554DA6D77FD463A60ABEDE4C582AE76F8552`.

### M304 actual cut-boundary kernels (2026-09-19 UTC)

For the original finite simply connected WB3 complex K and a connected
closed interior PL2 surface L in real ambient dimension three,
`SurfaceCutKernel` now constructs an actual finite connected orientable
closed cut piece R inside K, its exact boundary including old-boundary
pieces, and an actual boundary-component label whose space equals L.
That boundary inclusion has a proved nontrivial fundamental-group kernel.
The collar retains the original K,L and the prescribed relative
neighborhood U.

The proof uses the native open collar cover and retractions. New explicit
zero-section/projection maps induce an overlap-to-L group isomorphism;
their composites through both native retractions are the literal closed
boundary inclusions. Connected dense manifold interiors identify the side
closures with the supplied finite cut manifolds. Equality with the actual
boundary component then transports the kernel without assuming it or
identifying the newly produced element with the original source element.
The general continuous-map theorem in `FundamentalGroup/Nullhomotopy`
converts it into a free loop essential in that component and null in R.

The actual geometric model keeps the original nonempty finite PL ball and
embedded beta-two torus throughout, and verifies the actual cut boundary,
kernel and essential free loop together. It produces no embedded disk.
General ambient-kernel transport without simple connectivity, nonseparating
cuts and the actual Moise252 proof remain open. Full Moise264 and arbitrary-
shell Moise304 are not marked complete.

All 22 declarations in four changed/new modules, 43 critical reuses, the
actual model and three helpers have standard transitive axioms; all 13
applicable linters pass with zero diagnostics. Five former public
signatures are unchanged. Both new leaves are registered once; the native
graph has 527 modules and 1024 edges without cycles or HurewiczLowDegrees.
Thirteen source-matching private receipt sets and the final audit are frozen
at `moise304-reading/surface-cut-kernel-checkpoint/`, manifest SHA256
`080A9AD86A7A930F66371D76EE824CCECDEB73D2DA387A6F02F7F400C0FA08AA`.
See HANDOFF_CODEX_M304.md for exact APIs and limits. No full-root build or
independent integration acceptance is claimed.

### M304 transfer of an original ambient inclusion kernel (2026-09-19 UTC)

`CollaredClosedCover` now constructs a nontrivial kernel into one actual
closed side from a nontrivial kernel of the original collared inclusion
into the ambient space. Ambient simple connectivity is removed. The proof
constructs the two open domain neighborhoods, identifies their overlap with
the collar range, and proves the zero-section, ambient-map and native
retraction squares commute with their based-group casts. Dense exclusive
sides supply the regular-closed and frontier identities needed to orient
the collar. Native van Kampen produces the new side element.

The general manifold-pair and actual boundary-component theorems in
`SurfaceCutKernel` use those maps on the same finite A,B and L in any
finite-dimensional real ambient space. The complete original-K producer
`exists_boundary_component_kernel_of_interior_inclusion` accepts the actual
source inclusion kernel and preserves K,L,U. It constructs an orientable
finite cut piece, exact boundary trace and actual boundary-component kernel
for connected K,L in real ambient dimension three. The earlier simply
connected results are now corollaries. Two redundant local-path-connectedness
instances are removed; eighteen other former public signatures remain.

The actual nonempty original ball and beta-two torus model invokes this
general producer and verifies its actual boundary kernel and essential free
loop together. The model ambient remains a ball. All 37 declarations in
five changed/new modules, 54 critical reuses, the model and three helpers
have standard transitive axioms; all 13 applicable linters pass with zero
diagnostics. The registered native graph has 527 modules and 1032 edges
without cycles or HurewiczLowDegrees.

Fifteen source-matching private receipt sets and the complete audit are
frozen at `moise304-reading/collared-closed-cover-checkpoint/`, manifest SHA256
`8F96C466CCC27FB5683F03258247AE40693FE8EFF66D16AD4CCC7E5DBF06C0EA`.
See HANDOFF_CODEX_M304.md for exact statements and maps. Full Moise264
component/ambient generality, nonseparating cuts, the actual Moise252 proof
and embedded essential disks remain open. No full-root build or independent
acceptance is claimed; arbitrary-shell Moise304 is not complete.


### M304 essential disks conditional on Moise252 (2026-09-19 UTC)

`SurfaceEssentialDisk` now consumes the explicit `h252 : Moise252` on the
actual boundary-component kernel produced in the original K. For finite
connected closed PL2 L in a finite preconnected WB3 K in ambient dimension
three, it produces an embedded essential disk in K minus the old boundary,
with exact intersection with the original L and nonnullhomotopic boundary
inclusion into L. It retains the prescribed-neighborhood collar. Avoidance
of the old boundary and transport from the actual boundary label are proved.

The connected nullhomotopy-neighborhood API produces a finite connected
ambient neighborhood containing the same actual nullhomotopy. It gives the
new disk producer in any prescribed simply connected open neighborhood.
The original-shell specialization retains X, S, B0 and B1, produces the
essential disk/circle and centered annulus, and connects those same objects
to the existing target-preserving compression theorem. The actual ball,
wall, caps and their trace equations remain explicit geometric inputs;
their general producer is not claimed.

Seven existing public signatures are preserved. All 15 declarations across
the three changed/new modules and unchanged actual consumer, 74 critical
reuse entries, two unconditional actual geometric models, two explicitly
h252-conditional models and three helpers have standard transitive axioms.
All 13 applicable linters and the final private audit pass with zero
diagnostics. The registered source graph has 698 modules and 1427 edges
without cycles or HurewiczLowDegrees.

23 source-matching private receipt sets are frozen at
`moise304-reading/essential-disk-checkpoint/`, manifest SHA256
`4C0794FAAC0C53E13EF333D6FCE8388E3AD08F80CC44A4379A7F6757CA7266B9`.
See HANDOFF_CODEX_M304.md for exact APIs, actual-model scope and receipt
time. No full-root build or independent acceptance is claimed. The actual
Moise252 proof, full Moise264 generality, general compression-ball geometry
and arbitrary-shell Moise304 remain open.


### M304 relative ball neighborhoods of the original spanning disk (2026-09-19 UTC)

The new registered SpanningDiskBallNeighborhood leaf proves two geometric
producers. exists_isPLBall_neighborhood_of_proper_disk starts with an actual
properly embedded PL disk in a finite WB3 K and a prescribed open U
containing that disk. Exhaustion and the native disk derived-neighborhood
theorem produce a finite PL3 ball B inside K and U, containing the entire
original disk and a relative neighborhood of every disk point. The disk
meets frontier B in exactly its original rim, and boundary K is a relative
neighborhood of that rim in frontier B.

exists_isPLBall_neighborhood_of_spanning_disk starts with the original
finite connected closed surface S inside a finite preconnected WB3 K in
ambient dimension three, and the actual original D/r in interior K with
D intersect S equal to its rim. Connectedness of the disk interior puts
the whole disk in one actual cut side; density recovers its boundary.
The first producer is applied on that side inside U intersect interior K.
It produces B containing the same D, with D minus S in interior B,
D intersect frontier B equal to the rim, S intersect B contained in
frontier B, and S a relative neighborhood of the rim in frontier B.
No relative product chart or final compression ball/cap package is an input.

The new actual-model consumer retains the original beta-two torus, ball,
h252-produced essential disk and U = interior K and checks all these
properties together. The geometric producers themselves do not use h252.
The audit separately retains two unconditional geometry models and three
h252-conditional consumers. All 17 declarations in the audited layer,
79 critical reuse entries, five models and three helpers have standard
transitive axioms; all 13 applicable linters and the final private audit
pass without diagnostics. The two new declarations and their actual
derived-disk and centered-prism dependencies have fresh private receipts.

Twenty-six source/object/receipt sets and complete audit evidence are frozen
at `C:/Users/liao9/AppData/Local/Temp/moise304-reading/relative-ball-checkpoint/`.
Manifest SHA256: `31444C22AB47B279280A535C0D73EB291839B2BE58F8A3409E4024B9F7277E8A`.
Final audit completion: 2026-09-19T19:34:51.8777909Z. The new native import graph has 508
modules and 1000 edges, is acyclic and avoids HurewiczLowDegrees.
This is a dependency-closed checkpoint inside the ongoing compression-ball
round. The smaller centered prism, exact side wall and disjoint cap
construction are not yet delivered by this checkpoint. No other lane
source or shared output is changed; the stopped root build is not restarted.


### M304 compression balls for the same original disk and shell (2026-09-19 UTC)

Done in this feature branch, pending independent integration acceptance:
the geometric compression producer no longer requires a supplied product
neighborhood, compression ball, side wall, caps, or equivalent final geometry.
The preceding relative-ball layer is checkpoint 714b1599a29980d7fb7e74571a838fbb26475ff5.

SpanningDiskPrism proves the centered-prism construction and its boundary
geometry. IsPLBall.exists_centered_prism_subset_of_boundary_neighborhood
uses the native centered-prism theorem on the same original D/r, then
compactness of the standard rim to choose one positive thickness whose
entire side wall lies in the original surface. Strictly smaller thickness
excludes both old end faces. Injectivity gives exact surface trace.
IsCombinatorialManifold.exists_centered_prism_neighborhood_of_spanning_disk
constructs the needed auxiliary ball internally from the original finite
connected closed surface and disk, in any prescribed open U containing D.
The auxiliary ball and cut side are not hypotheses of this public result.
IsPLHomeomorphOn.exists_wall_and_caps_of_centered_prism takes the two actual
end faces of that same prism and proves their disjointness, exact frontier
union, cap/wall intersections, and both labeled rim identities. Its
intermediate prism input is produced by the preceding theorem.

SpanningDiskCompression exposes
IsCombinatorialManifold.exists_compression_neighborhood_of_spanning_disk.
For the same D/r and S it returns N, W, D0/D1, f, rho, r0/r1, with
N a PL3 ball contained in U, D contained in N, D minus S inside interior N,
D intersect frontier N equal to the original rim, and N a relative
neighborhood of all D in S union D. The prism has f(x,0) = r(x).
S intersect N equals W; W is a relative neighborhood of the rim in S.
The rim parameterization satisfies rho(r(x),t) = f(x,t), fixes the rim at
t = 0, and matches the two cap boundary labels exactly. The caps are
disjoint and frontier N = W union D0 union D1. W and the caps are chosen
compatibly from this D, not from an arbitrary previously selected annulus.
The neighborhood proof uses only the annulus-complement leaf, without an
import of the higher compression-separation consumer.

SphericalShellCompression exposes
IsSphericalShell.exists_compression_of_essential_disk. It preserves the
given X, B0, B1, S, D/r and prescribed U, constructs all the above geometry
inside U intersect interior X, and applies the unchanged separation/Betti
consumer to produce an actual connected component P of the capped surface.
P remains in interior X, separates the same B0/B1, and has strictly smaller
bettiOne than S. No Loop Theorem hypothesis is needed once the actual
essential disk is supplied. Its sibling
IsSphericalShell.exists_separating_component_bettiOne_lt_of_loop_theorem
obtains that disk using the explicit h252 input and gives strict Betti
decrease for an arbitrary nonspherical connected separator in the same shell.

Verification: all three new modules compile without diagnostics; the
compression leaf and shell consumer were rebuilt after narrowing imports.
All 25 declarations in the cumulative native audit, 84 critical reuse
entries, eight actual models and three model helpers have only approved
foundational axioms. All 13 applicable linters pass. The eight models are
three unconditional models and five explicit-h252 conditional consumers.
The new unconditional and conditional compression models both retain a
nonempty actual disk in the original beta-two torus and shell with nonempty
targets, and quantify over every open neighborhood of that same disk.
They check all ball/wall/cap, centered parameterization, relative neighborhood,
component, target and Betti conclusions together. A separate conditional
model consumes the new arbitrary-shell strict-decrease theorem directly.

Thirty source/object/receipt sets and the complete audit are frozen at
`C:/Users/liao9/AppData/Local/Temp/moise304-reading/compression-checkpoint/`.
Manifest SHA256: `7FE6FE9B969793268DA6857A4880FA26962828724136D282FC88181C73CF5C4B`.
Final zero-diagnostic audit completion: 2026-09-19T19:59:17.5691222Z.
The native import graph has 907 modules and 1927 edges, is acyclic,
and avoids HurewiczLowDegrees. All three leaves are registered in the flat
root. The owner-stopped root build was not restarted; all output is private.
No other lane source or shared object is modified.

Remaining scope: the actual Moise252 proof, broader Moise264 generality and
the final arbitrary-shell Moise304 endpoint/integration are not claimed here.
The previously reported missing ball/wall/cap producer for an original
essential disk is closed by this round. Independent acceptance remains with
the coordinator; the feature branch audit is not an acceptance substitute.


### M304 arbitrary-shell sphere endpoint from the Loop Theorem (2026-09-19 UTC)

Author-verified in this feature branch; independent integration acceptance is
pending. The only native change is thirteen added lines in the existing
SphericalShellCompression leaf: moise304_of_moise252 (h252 : Moise252) : Moise304.
There are no deleted native lines, new modules, signature changes or extra
public wrapper declarations. MoiseChain, the E3 lane and the h-circle lane
are unchanged.

The exact conclusion quantifies over every original X, B0, B1 in Euclidean
three-space with IsSphericalShell X B0 B1, and constructs B with IsPLSphere 2 B,
B contained in interior X and Separates B B0 B1. The proof obtains an actual
connected separator minimizing bettiOne from the existing native selection
theorem. If it is not a sphere, the previous compression producer supplies a
connected separator with strictly smaller bettiOne in the same shell and for
the same targets, contradicting minimality. The supplied hypothesis is only
h252; no disk, annulus, compression ball, minimality or sphere is assumed.

The unchanged moise305_tame_of_moise304 consumes moise304_of_moise252 h252.
This gives the full existing Moise305Tame statement: the original two nested
topological cells and their shell, with a bicollared outer frontier, produce
an actual intermediate PL3 ball. Its native proof uses SphereNesting and the
proved PL Schoenflies chain. No extra Schoenflies hypothesis was introduced.

Two new explicit-h252 models use the concrete nonempty norm band 1 <= norm <= 2
and the same spheres of radii one and two. One constructs the separating PL2
sphere; the other constructs an actual PL3 ball containing the closed unit
ball in its interior and contained in the radius-two open ball. The latter
also verifies its nonempty PL2 frontier lies in 1 < norm < 2 and separates the
same targets. The outer bicollar is constructed by radial exponential scaling.
The previous three unconditional disk/ball/compression models are retained.
These conditional consumers do not independently prove Moise252.

The complete audit checks 31 nonautomatic native declarations, 91 critical
reuse entries, ten models (three unconditional, seven with explicit h252),
and three model helpers. All transitive axiom closures contain only the
approved foundational axioms; all 13 applicable linters pass. The endpoint,
unchanged tame consumer and SphereNesting have zero-diagnostic private
compile receipts. Other frozen dependency receipts retain their actual dates.

A separate kernel-body and type dependency traversal covers 9309 native
constants for moise304_of_moise252 and 7184 for the tame consumer. It includes
private declarations and records every edge and non-native boundary module.
Neither closure contains Moise303 or wide Moise264. Live source search finds
only the Moise264 definition in MoiseChain, not a use in this chain; no
Moise303 declaration is present in this checkout. The book route and E3's
separate 30.3 proof are therefore not prerequisites of this compiled route.
This does not claim the full wider Moise264 statement has been proved.

Thirty-three source/object/receipt sets and all evidence are frozen at
`C:/Users/liao9/AppData/Local/Temp/moise304-reading/shell-endpoint-checkpoint/`.
Manifest SHA256: `6D9EBB844D1C8660963E136D047B81C29BD62CD9F70D06F699EE47BEB59FDEE6`.
Final zero-diagnostic audit: 2026-09-19T20:22:52.2507249Z. The interval from the first successful
endpoint compile to this final audit is 782.934 seconds; it is not a
measurement of the entire round's effort. The source import closure contains
910 native modules and 1934 edges, is acyclic and avoids HurewiczLowDegrees.
The existing leaf remains registered in the unchanged flat aggregate.
The owner-stopped root build was not resumed; shared outputs were untouched.

Remaining inputs and acceptance: Moise252 is still an explicit upstream
input; Moise305Tame retains its bicollared-outer-frontier condition. Neither
unconditional Moise304 nor general Moise305 is claimed. The arbitrary-shell
conditional endpoint is now closed in the author lane, pending the
coordinator's independent replay and integration acceptance.


### M304 original toroidal-shell incompressibility and fundamental groups (2026-09-19 UTC)

Author-verified mathematical checkpoint; Moise306 and Moise307 remain open.
Six new leaves and one existing leaf contribute 595 added native lines,
zero deleted native lines, 34 source declarations and one generated local
notation constant. The flat aggregate gains exactly six imports. Existing
declarations in SurfaceEssentialDisk and all other earlier APIs are unchanged.
MoiseChain and other lanes are unchanged; independent integration is pending.

The new actual-kernel disk producer in SurfaceEssentialDisk takes a nonidentity
loop killed by the inclusion into its prescribed open neighborhood, without
an ambient simple-connectivity assumption. SurfaceIncompressibility then
constructs a lower-Betti connected separator for the same two targets from
that kernel. A minimal separator consequently has injective inclusion on
fundamental groups. All disk and compression geometry is produced using the
explicit upstream Moise252 input and the existing checked relative machinery.

Manifold.CylinderImage proves the interior and frontier formulas for embedded
compact manifold cylinders by invariance of domain. ToroidalShell applies
them to the original homeomorphism in IsToroidalShell Y T0 T1: frontier Y is
exactly T0 union T1, and interior Y is homeomorphic to the torus times (0,1).
It constructs a finite connected oriented two-sided PL2 separator in this
original interior and an actual minimum of bettiOne for these original
targets. ToroidalShellCompression's
IsToroidalShell.exists_connected_separating_surface_fundamentalGroup_map_injective
produces that separator with injective inclusion into interior Y from h252.
No minimum, sphere, torus, compression disk or classification is assumed.

FundamentalGroup.Torus computes the torus group at every basepoint as Z x Z.
ToroidalShellFundamentalGroup transfers this to both Y and interior Y and
proves both actual endpoint inclusions T0 -> Y and T1 -> Y induce bijections
on fundamental groups. These are the native group inputs for the book's
sphere-exclusion argument, not a completed sphere-exclusion theorem.

The new unconditional model starts from the existing actual embedded PL
torus, constructs its ambient bicollar, and restricts that embedding to a
closed unit cylinder. Its shell, interior and both targets are nonempty;
the targets are disjoint; its interior is proved not simply connected.
A second unconditional model constructs its minimum separator. A third,
with explicit h252, constructs an incompressible separator of exactly those
same targets and proves its fundamental group commutative. No standard
shell is substituted for the arbitrary shell in the public results.

The cumulative audit checks 66 nonautomatic native constants (including the
local notation constant), 106 critical reuse entries, thirteen models (five
unconditional, eight with explicit h252), and four model helpers. Every
checked transitive axiom closure uses only the approved foundational axioms,
and all 13 applicable linters pass. Every changed leaf has a private compile
receipt with zero diagnostics. Kernel type-and-body traversals for the
separator, interior group computation and left endpoint inclusion contain
no Moise303 or wide Moise264. The source import closure has 912 native
modules and 1938 edges, no cycles or HurewiczLowDegrees.

Frozen evidence: C:/Users/liao9/AppData/Local/Temp/moise304-reading/toroidal-checkpoint
contains 39 source/receipt sets, raw and normalized source identities,
AuditToroidal.lean, toroidal-census.json, ToroidalModels.lean, source review,
compiled dependency closures and timing. Manifest SHA256: 215C4D6BFEE73F394D4B8908EB424E518FD5BFAEDAB99EABAE3827865521560C.
Final zero-diagnostic audit: 2026-09-19T21:07:56.0084065Z. The compile-to-audit window is
1660.493 seconds, not total effort.
The owner-stopped root build remains stopped; shared artifacts are untouched.

The remaining geometric obligations are exact: (1) a PL2 sphere in interior Y
cannot separate T0 and T1, using the actual cut sides and the endpoint group
isomorphisms; (2) a connected closed orientable finite PL2 surface with the
resulting nontrivial fundamental group embedded in Z x Z is homeomorphic to
S1 x S1. The current SurfaceInvariants API computes counts from an already
supplied handle profile; it does not construct that profile or a torus
homeomorphism. SurfaceSphereRecognition handles Euler characteristic two,
not the required Euler-zero orientable case. Betti number two alone has not
been used as torus recognition. Work toward these obligations continues;
this checkpoint does not claim Moise306, Moise307 or Moise252 complete.


### M304 parity and commutative-cover primitives; exact recognition frontier (2026-09-19 UTC)

The preceding original-shell layer is committed and pushed as
6f227c0576feb906bb14e8bb693bc8e7d0fdaf72. Its 39 frozen source/receipt sets were
checked again against working-tree raw bytes, committed normalized bytes,
and all artifact hashes. This follow-on layer adds two registered leaves,
three proved declarations and 90 native lines, with zero deletions or
changes to previous declarations. Across the toroidal round this is
685 native lines, eight new leaves and 37 source declarations plus
one generated local-notation constant.

SurfaceEulerParity proves
IsCombinatorialManifold.even_eulerChar_of_finrank_eq_three and
IsCombinatorialManifold.even_bettiOne_of_finrank_eq_three for any connected
finite closed PL2 surface in a three-dimensional real normed space.
The proof produces its actual bounded PL3 filling with that exact boundary,
uses the boundary Euler formula, and uses the already proved orientability
and rational Euler-Betti formula. No handle profile or parity assumption is
introduced. The added unconditional models check an actual embedded torus
and the actual minimum separator in the non-simply-connected shell model.

FundamentalGroup.CommutativeCover proves
simplyConnectedSpace_or_of_open_cover_of_isMulCommutative. For a two-set
open cover with path-connected sides and simply connected intersection,
commutativity of the ambient fundamental group forces at least one side
to be simply connected. The proof applies the native van Kampen free-product
isomorphism and proves two nonidentity letters from different factors cannot
commute by uniqueness of reduced words. Ambient simple connectivity is not
an assumption. This closes the group's free-product obstruction on book
page 217, but does not yet construct the actual cut cover of the original Y.

The round reaches two explicit geometric frontiers. First, for the ORIGINAL
IsToroidalShell Y T0 T1, prove that no IsPLSphere 2 S with S inside interior Y
can satisfy Separates S T0 T1. Required construction: the closures of the
two components of Y minus S, their path connectivity and regular-closed
properties, a collar contained in original Y, the corresponding open cover,
and factorization of the two actual endpoint maps through their own sides.
The group isomorphisms and commutative-cover obstruction are proved; the
closed-cover kernel theorem is for actual nontrivial boundary kernels and
cannot substitute for this sphere case. The older negative/positive collar
cover intersection API assumes the ambient space simply connected and
therefore cannot be instantiated at this toroidal Y.

Second, construct a torus homeomorphism for a connected closed orientable
finite PL2 surface with nontrivial commutative fundamental group (here it
embeds into Z x Z). The weaker intermediate numerical statements do not
give that homeomorphism. SurfaceInvariants only starts from a supplied
handle/crosscap profile; SurfaceSphereRecognition only treats Euler
characteristic two. A native polygonal presentation/classification or a
proved orientable Euler-zero torus-recognition construction is missing.
The PI1-to-integral-H1/abelianization step used by the book is also not
supplied by the checked path-cone vanishing API. No blocked HurewiczLowDegrees
import, new axiom, sorry or conclusion-shaped hypothesis has been added.

Moise306 remains PARTIAL at these actual geometric interfaces. Moise307 is
not started, in accordance with the required 30.6 -> 30.7 order. Neither the
incompressible separator nor parity is reported as IsPLTorus, and the
explicit upstream Moise252 input remains unresolved. Independent integration
acceptance remains pending.

Final cumulative verification: 69 nonautomatic native constants, 112 critical
reuse entries, fifteen actual models (seven unconditional, eight with h252),
four model helpers, and all 13 applicable linters. All audited axiom closures
contain only the approved foundational axioms; changed-module compiles and
the full audit have zero diagnostics. Five kernel body/type traversals show
no Moise303 or wide Moise264. The source graph has 940 native modules
and 2019 edges, with no cycle or HurewiczLowDegrees.
The owner-stopped root build was not run; shared outputs remain untouched.

Frozen final evidence: C:/Users/liao9/AppData/Local/Temp/moise304-reading/recognition-final-checkpoint
contains 41 source/receipt sets, the complete audit/census, actual models,
kernel dependency reports and source/timing review. Manifest SHA256:
D04395C683F14D90E0886B7F637B0E536E8E7F6DC1F6103CF98120009B7D9F87.
Final zero-diagnostic audit: 2026-09-19T21:21:28.6825480Z; 2473.167 seconds since the first
successful changed-module compile, not a measurement of total effort.


## M304 original toroidal-shell sphere exclusion checkpoint, 2026-09-19

This entry supersedes the sphere-exclusion frontier of checkpoint 8236587e5.
The arbitrary ORIGINAL IsToroidalShell Y T0 T1 now satisfies
IsToroidalShell.not_separates_of_isPLSphere: an IsPLSphere 2 S contained
in interior Y cannot separate the original endpoint sets T0 and T1.
This theorem has no Moise252 input. The finite-surface corollary
IsToroidalShell.not_simplyConnectedSpace_of_separates also has no Moise252
input. Combining it with the existing minimum/compression producer gives
IsToroidalShell.exists_non_simply_connected_separating_surface_fundamentalGroup_map_injective
with the same explicit h252 input as before.

The sphere proof constructs the Schoenflies ball D with frontier D = S.
Its actual closed sides in Y are P = val^(-1)(D) and
Q = val^(-1)((interior D)^c). Frontier S inside interior Y gives the exact
relative closure equalities closure(P \ Q) = P and closure(Q \ P) = Q.
A given sphere collar is shrunk into interior Y and codomain-restricted to Y.
The collar determines an open cover whose intersection is exactly its range.
Connectedness of the closed sides follows from the connected closed-cover
intersection; open collar neighborhoods are path connected and retract to
the actual sides. No side, regularity, connectivity, intersection identity,
kernel, or non-sphere hypothesis is supplied by the caller.

The simply connected sphere makes the collar intersection simply connected.
The commutative-cover obstruction therefore makes P or Q simply connected.
Schoenflies component connectivity and the ORIGINAL separation relation put
T0 and T1 in opposite actual sides. Each actual endpoint inclusion T_i -> Y
is written as T_i -> P -> Y or T_i -> Q -> Y. A simply connected middle
space makes its fundamental-group map trivial, contradicting the checked
surjectivity of that actual endpoint map onto pi1(Y) isomorphic to Z x Z.
All pre-existing public signatures are preserved; the old closed-cover kernel
proof now reuses the extracted open-cover construction.

Changes: 389 native lines added, 53 removed; eleven new declarations,
four new leaf modules registered in the flat root, eight changed native modules.
Cumulative verification covers 87 nonautomatic native constants, 119 critical
reuse entries, eighteen actual models (nine unconditional and nine conditional
on h252), four model helpers and all thirteen applicable linters. Every audited
axiom closure is a subset of propext, Classical.choice and Quot.sound. Fresh
changed-module compilation and the complete audit produced zero diagnostics.
Nine exact kernel type/body dependency traversals contain no Moise303 or wide
Moise264. The source import graph has 951 modules and
2049 edges, with no cycle or HurewiczLowDegrees.
The explicit owner stop on the root build remains in force. Shared outputs
were not changed. Independent integration replay is still pending.

The remaining Moise306 frontier is the actual torus homeomorphism of the
produced connected closed orientable finite PL surface, now proved non-simply
connected and with fundamental group injecting into pi1(interior Y) = Z x Z.
SurfaceSphereRecognition supplies only Euler-characteristic-two recognition;
SurfaceInvariants consumes a supplied handle/crosscap profile. Neither proves
the needed torus recognition. The checked PathCones/FieldPathCones API proves
degree-one homology vanishing under simple connectivity, not the general
pi1-to-integral-H1 abelianization comparison needed by the book's rank argument.
No numerical invariant or supplied profile is being counted as IsPLTorus.
Moise307 remains unstarted, and Moise252 remains an explicit unresolved input.

Before later Moise307/308 consumers, repair the Moise308 spine contract:
the book's inner S1 spine must generate pi1 of every intermediate S through
the actual inclusion map. The current contract assumes a spine of intermediate
S itself. Preserve that true result, add the missing inclusion transport, and
do not consume Moise312/314 until this transport is proved. MoiseChain was not
edited in this checkpoint.

Frozen evidence: C:/Users/liao9/AppData/Local/Temp/moise304-reading/sphere-exclusion-checkpoint
45 source/receipt groups. Manifest SHA256: 69B2B74D52D5C659058B905AB9B216AF35F0FAF4CDAB3F5B14EB22E04ABFE701.
Complete zero-diagnostic audit: 2026-09-19T21:54:51.8379979Z.
Kernel dependency audit: 2026-09-19T21:57:34.0194709Z.


## M304 degree-one Hurewicz homomorphism checkpoint, 2026-09-19

The original toroidal-shell sphere exclusion from 87826c69c remains unchanged.
A general integral degree-one Hurewicz homomorphism now exists for every
based topological space. hurewiczOne_surjective proves its surjectivity for
every PathConnectedSpace, with no simple connectivity, manifold, compactness,
local path connectivity, or finite complex assumption.

PathConcatenation gives an explicit singular triangle for any composable
paths; its boundary is q - (p.trans q) + p. PathHomotopy triangulates an
arbitrary endpoint-fixed path homotopy into two singular triangles, with
constant-path corrections, and proves that homotopic path chains differ by
a boundary. HurewiczOne descends the resulting loop class to the actual
fundamental group, respecting Mathlib's reversed concatenation convention.
Surjectivity closes every singular edge using chosen basepoint paths; their
endpoint corrections cancel for every cycle. The proof compares the actual
linear maps on the singular-chain basis and then uses the cycle quotient.

Three new leaf modules, 384 native source lines, eighteen public and four
private declarations; all three are registered in the flat root. Every
changed module compiled with zero diagnostics. The cumulative main audit
checks 109 native constants, 133 critical reuse entries, twenty models and
four helpers under all thirteen applicable linters. A separate checked model
adds two reuse entries and one actual circle model: there exists an actual
loop whose integral homology coordinate is exactly 1, using the independently
checked sphere top homology equivalence. The other two new models exercise
surjectivity on the circle and torus with explicitly nontrivial fundamental
groups. Thus the cumulative evidence has 135 reuse entries and twenty-one
models (twelve unconditional, nine retaining h252).

All checked axiom closures contain only a subset of propext,
Classical.choice and Quot.sound. Twelve actual kernel type/body dependency
traversals are nonempty and avoid Moise303 and wide Moise264. The native
source import graph has 954 modules and 2052 edges,
with no cycle or HurewiczLowDegrees. No shared outputs were changed. The
explicit owner root-build stop remains in force; integration replay is pending.

This checkpoint proves the map and its surjectivity, not the abelianization
isomorphism, rational coefficient comparison, Betti-one rank bound, or actual
surface-to-torus homeomorphism. Those remain the Moise306 recognition frontier.
Moise307 is not yet started. Moise252 remains an explicit unresolved input.
The earlier Moise308 original-inner-spine inclusion-transport obligation is
unchanged; MoiseChain and other lanes were not edited.

Frozen evidence: C:/Users/liao9/AppData/Local/Temp/moise304-reading/hurewicz-one-checkpoint
48 source/receipt groups. Manifest SHA256: 53E017AC78CAC17877AF7EF20F662CFB3602F1E09405B05B4884F4F01E891D84.
Main audit: 2026-09-19T22:35:19.9060986Z.
Circle model audit: 2026-09-19T22:39:46.2922313Z.
Kernel dependency audit: 2026-09-19T22:33:14.9531106Z.


## M304 original-shell Betti-two checkpoint, 2026-09-19

The actual incompressible separator in the original prescribed toroidal shell
now has rational first Betti number exactly 2 and Euler characteristic 0.
IsToroidalShell.bettiOne_eq_two_of_separates_of_fundamentalGroup_map_injective
uses injectivity of the actual inclusion at one actual basepoint. It requires
no Loop Theorem input once that injectivity is supplied. The existence endpoint
IsToroidalShell.exists_separating_surface_bettiOne_eq_two retains the explicit
unresolved h252 : Moise252 and returns the same original-shell separation,
containment, two-sidedness and every-basepoint inclusion injectivity.

FieldCycles gives the linear cycle quotient. FieldHurewiczOne constructs the
field-coefficient degree-one map and proves that its image spans first homology
for every PathConnectedSpace. This is a spanning statement, not set surjectivity
over an arbitrary field. FundamentalGroupRank proves the natural upper bound
when the fundamental group embeds in the multiplicative group of a finitely
generated torsion-free abelian group: use its finite free integer basis and the
field spanning theorem. For the actual shell inclusion the target is Z x Z,
so Betti one is at most 2. The checked embedded-surface parity and original-shell
sphere exclusion then give equality. No abelianization-isomorphism theorem or
unproved coefficient-comparison theorem is assumed.

Four new leaf modules, 408 native source lines, twenty public and four
private declarations; all four are registered in the flat root. Each compiled
with zero diagnostics. The cumulative main audit checks 133 native constants,
143 reuse entries, twenty-four models and four helpers under all thirteen
applicable linters. The retained independent integral-circle unit-coordinate
model adds two reuse entries and one model: total 145 reuse entries and twenty-five
models (fifteen unconditional, ten retaining h252). New models check arbitrary
field rank bounds on Circle and Circle x Circle, the actual original-shell
Betti-two separator, and a nonzero rational Hurewicz image on an independently
constructed actual embedded torus.

All checked axiom closures contain only a subset of propext, Classical.choice
and Quot.sound. Sixteen kernel type/body closures are nonempty and avoid
Moise303 and wide Moise264. The native import graph has 958 modules and
2060 edges, no cycle, and no HurewiczLowDegrees dependency.
No shared outputs changed. The explicit owner root-build stop remains active;
integration replay is pending.

Actual torus recognition remains open: no homeomorphism has yet been produced
from these numerical invariants, so Moise306 is partial and Moise307 has not
started. A concrete next route is an actual essential spanning disk (using
h252), nonseparating compression to a sphere, then the checked spherical disk-pair
matching, cylindrical gluing and orientable monodromy APIs to reconstruct the
surface-to-torus homeomorphism. These are remaining obligations, not conclusions
of this checkpoint. MoiseChain, the original-inner-spine Moise308 obligation,
and other lanes remain unchanged.

Frozen evidence: C:/Users/liao9/AppData/Local/Temp/moise304-reading/shell-homology-checkpoint
52 source/receipt groups. Manifest SHA256: C94B17E527CA290BE0D767A75548E3235E77ED4723C30B6D456E4A4E1307A751.
Main audit: 2026-09-19T23:03:40.1144416Z.
Kernel dependency audit: 2026-09-19T23:05:08.6478958Z.
### Resumed-stage cylinder gluing gate

M304 734c87b5f is independently accepted: three existing cylinder/meridian
interfaces have weaker gluing hypotheses, and all seven affected module suites
pass together. The renamed cap theorem is not a new theorem count. The actual
solid-torus fixtures remain untwisted. Arbitrary prescribed-shell geometry and
Moise304 remain open. New-stage accounting is in RESUMED_ACCEPTANCE_20260919.md;
the prior morning report is unchanged. See integration handoff section 70.

### Finite surface-splitting representation and cap gate

E3 through 5877584aa is independently accepted with canonical gluing reuse.
An actual three-dimensional prism and actual solid-torus compression test
exercise the new physical caps and finite surface representation. Five public
results and one private helper are new; duplicated old gluing proofs are not
new results. General 30.3 still needs the relative chart identifying original
surface end circles with prism slices. See integration section 71 and the
resumed-stage acceptance ledger. No full-root compilation is claimed.

### Actual boundary charts and the remaining relative normalization gate

The four F boundary-chart leaves through f0482b620 are independently accepted:
actual bicollar, open product with the original PL parameter, compatible
boundary-plane chart, and exact half-space sign. An actual tetrahedron vertex
lies on the tested double frontier. Ten native declarations pass complete
axiom and thirteen-linter checks, together with six existing declarations
from two previously unreachable prerequisites. Those modules now have
required headers and direct root imports. One old unused finite-dimensional
hypothesis was removed, preserving the proof and old caller. See integration section72 and the resumed
ledger. At that checkpoint the boundary perturbation/homotopy queue and
a50bc58dd/44d4e28ef consumers awaited replay; section 73 records acceptance.

The current F lane must produce relative crossing control in the active
transition annulus, or a finite protected-core invariant with a proved cover
of the original target. Closed-region protection outside the new point alone
does not establish overlap preservation. The fixed-vertex obstruction to
the older face-transversality interface must remain explicit. Neither
global normal form nor the loop theorem is complete. Other current lanes
continue original-surface prism compatibility (E3), prescribed-shell
separation-preserving compression (M304), graph-fixed compatible PL
neighborhood modifications (h), and actual relative critical-pair normal
form geometry (S). No full-root compilation is claimed.


The historical unaccepted queue at section 72 contained h d2c94f911, M304
f2338f0d and S f15aad47d; sections 73-74 supersede that queue.
Source review distinguishes h's graph-fixed external homeomorphism from a
self-homeomorphism of the original K.space; the latter is its next producer.
M304's new finite polyhedral separator is not yet a capped closed surface.
S's actual compact regular-band product still needs critical endpoint gluing
and genuine cancellation incidence. These are next-round obligations, not
independently verified theorem completions of their final goals.

### Boundary homotopy accepted; original geometric producers still required

Integration section73 independently accepts F's nine frozen boundary
perturbation/loop/homotopy/relative modules through44d4e28ef, together with
two previously unreachable half-space prerequisites. All 38 native
declarations, 48 key reuse entries, thirteen linters and classified probes
pass. Twenty-five declarations are new; old code and conditional fixtures
are counted separately. Supported local perturbation now preserves the
actual boundary loop class inside its original normal neighborhood.
Closed-set protection leaves the active transition region open, and the
embedded disk in the smaller normal system is still an input. Global
normalization and the loop-theorem endpoint remain incomplete.

E3's latest source throughddade8562 remains queued for independent acceptance.
Its source audit corrects the proposed outer-circle marking: those circles
avoid the small neighborhood. Continue with actual inner-disk boundary
traces, the produced half-ball outer-boundary inclusion, sphere disk choice,
and original external-annulus gluing. Do not infer that original outer
circles lie inside that local neighborhood. Canonical finite realization
and manifold capping from ab29 remain the downstream implementation.

M304's bed13ca15 is a queued genuine capped-union separation proof, not
completion of arbitrary-shell30.4. The native Betti and separating-component
consumer already exists; its next round advances the actual original-wall
and complement geometry rather than duplicating that chain. S's ec69dc759
produces a real saddle section from original Morse data and a unique
descending trajectory, still queued. The minimum end and two-end relative
flow strip must preserve that same trajectory/field and original atlas.
The regular-band theorem's separately constructed field cannot supply the
original trajectory's incidence without a proved comparison.

Five tasks remain authorized without a new deadline. Administrative leases
are renewable and are not owner deadlines. Existing hourly quiet follow-up,
two private checker slots and no unsolicited full-root rebuild continue.


### Actual compression component accepted; interior essential disk is next

Integration section 74 accepts M304 through 01fc05b8c, including its preceding
common solid-torus neighborhood, polyhedral separator and genuine wall-to-caps
separation checkpoints. From an actual original essential disk/circle and the
marked compression ball/caps, the endpoint produces a connected closed PL2
component of the literal capped union, separates the original targets and
strictly lowers the first Betti number. The result surface and final separation
are not hypotheses. The exact component equation is proved, with the previous
selection signature retained. All 68 declarations in fifteen fresh modules,
63 critical reuses and six actual model assertions pass axiom and lint audit.
The six assertions share one concrete nonseparating torus family.

Do not repeat the existing minimum-Betti selection or capping arithmetic.
M304 now advances actual cutting along an internal two-sided surface and the
fundamental-group kernel bridge from the corrected boundary-loop theorem to
the corrected Moise264 contract. Moise252 may be a named, explicit unresolved
upstream input; a proper embedded disk or equivalent final kernel witness may
not be assumed as the new producer's conclusion in disguise. Preserve the
original K, L and ambient neighborhood. E3 independently retains original-wall
alignment, inner-disk traces and physical cap gluing. Both gaps remain needed
for arbitrary-shell Moise304.

Pending independent acceptance is E3 through ddade8562, h through d2c94f911
and S through ec69dc759. F's boundary layer through 44d4e28ef and M304 through
01fc05b8c are accepted. Later active-round source must be frozen at delivery
before integration. Required dependency refresh is authorized privately and
on demand; source ownership, hourly quiet follow-up and checker limits remain.


### Relative prism and outer-boundary layer accepted

Integration section 75 accepts E3 through ddade8562, including actual marked
boundary-circle prism coordinates and stronger split-ball outer-boundary
inclusions. The sphere disk selector now works for any preconnected obstacle
and lives in SphereSchoenflies; its earlier disk-specific interface is retained.
Five fresh modules, all 22 native declarations, fifteen key reuses and thirteen
linters pass independent verification. This does not supply the actual marked
disks or physical caps from all Moise303 data. Continue E3's inner-disk boundary
replacement and gluing of original outer annuli. Do not place the original
outer circles inside the small derived neighborhood that avoids them.

The independent acceptance queue is h through d2c94f911, S through d77f16c3c
and F through 71b0b003e. F's completed flat-sheet round has resumed toward a
controlled extension matching actual inner perturbations, then compatible
transition-region coverage; its prior crossing layer through44d4 is accepted.
S is on actual strip differential invertibility and critical-endpoint gluing.
M304's original-shell compression component layer remains accepted, while
actual Moise264 cutting/kernel production is open. Existing five tasks retain
their lanes, with no new deadline, no routine mid-round messages and no
time-triggered full-root rebuild.


### Relative perturbation stability accepted; next actual geometric gates

Integration section 76 accepts h through d2c94f911: finite perturbation radii,
actual supported PL moves fixing the original graph, and image-neighborhood
trace transport. Eight fresh modules, 33 native declarations, seventeen key
reuses and thirteen linters pass independent verification. Of twelve newly
placed declarations, two are relocated proofs; ten are new mathematics.
The original three-dimensional carrier is not proved invariant. Continue h's
active carrier-preserving self-homeomorphism and compatible-subdivision round.

Independent acceptance now queues S through c0f4df1b1 (including d77f16c3c and
earlier unaccepted prerequisites), F through 71b0b003e, and M304 7a1632779.
S has delivered actual open smooth strip coordinates and has resumed full
Morse endpoint gluing and supported cancellation. M304 has delivered actual
finite cut pieces and open-side kernels and has resumed the compatible maps
from open sides to the same closed boundary components; corrected Moise252
remains explicit unresolved upstream. F owns the controlled canonical half-space
extension/general-position implementation for the same actual perturbations.
E3 remains on original inner traces and physical caps. These are completed-round
handoffs, not new parallel lanes. No full-root restart is triggered by elapsed
time, and no new deadline has been inferred.


### Actual Morse flow coordinates accepted; current five-lane gates

Integration section 77 independently accepts S through c0f4df1b1, including
d77f16c3c and its earlier frozen prerequisites. Fourteen fresh modules, all
49 native declarations, 63 distinct external reuses, and 55 model declarations
from three concrete families pass. The source adds 43 native declarations
(36 public, seven private), with +2081/-0 Lean lines including thirteen root
imports. The actual saddle-level immersion and flow transversality produce an
open smooth inverse about the whole original closed strip and its two end
overlaps. A supplied cubic chart admits relative cancellation; constructing
the general endpoint-neighborhood gluing and supported elimination for the
original Morse pair remains the active S round. Compact PL smoothing remains
an independent unfinished headline.

The frozen independent-acceptance queue is now F 71b0b003e, M304 through
96ba235a4 including 7a1632779, h e85a235df and E3 c10b83586. Author delivery is
not independent acceptance. h's completed round now preserves the original
carrier and transports newly chosen canonical neighborhoods through compatible
subdivisions; the next round must produce their actual solid-torus type.
E3's physical cap construction now yields SurfaceSplitAndCap; separation of
the original H/Q by this same result is the next gate toward Moise303.
M304's actual boundary kernel is delivered for simply connected original K;
general original-inclusion kernel transfer remains the active next step.
Corrected Moise252 is still explicit unresolved upstream, and no embedded
essential disk or Moise264/Moise304 endpoint is claimed. F continues the same
actual perturbation's Lipschitz control in its canonical half-space files.

Five existing tasks retain one lane each. F/S/M304 use Astra max and h/E3 use
Sol max. Handoffs to the newly completed h and E3 rounds have been sent;
ongoing F/S/M304 rounds receive no routine status requests. The prompt and
resumed-stage ledger govern hourly follow-up without a new owner deadline.
Compilation remains limited to two private checkers, one per lane, and at most
one root worker and three Lean processes. The whole-root gate remains deferred;
its next run requires an actual compatibility or stalled-work reason, not an
elapsed-time trigger. Static root coverage is 9642 modules including the root.


### Flat-sheet relative perturbation accepted; actual interior-disk gate

Integration section 78 accepts frozen F 71b0b003e: one actual projected-disk
perturbation theorem and five geometric helpers. One sheet moves and the other
physical sheet remains fixed; a quantitative PL correction proves their
boundary and interior crossings. Actual source patches, disk domain, target C,
boundary preimage and small boundary homotopy are preserved. The theorem still
assumes simultaneous flat coordinates, local injectivity, at-most-two fibers
and a boundary-tangent displacement on J. Its explicit nonempty half-plane
model checks the geometric core, not a complete NormalSystem. Full transition
coverage, actual inner-perturbation matching and global relative normalization
remain F's active round in the canonical half-space files.

Six native declarations, seven key reuses, six mathematical fixture declarations
and one audit-only macro pass the full axiom/lint check. Accepted Lean is
+590/-0 including one root import. Root static coverage is 9643 modules;
the whole-root compilation gate remains deferred.

M304's new 41220900e general ambient-inclusion kernel layer is frozen with
7a/96 and still awaits independent acceptance. Its primary has removed ambient
simple connectivity; the full original-K producer still assumes connected K/L
and real ambient dimension three. The next round has been dispatched at its
completed delivery: use the actual boundary kernel and the explicitly unresolved
Moise252 to construct an essential embedded disk in the original K interior,
prove old-boundary avoidance and essentiality transport to L, and supply the
actual original-shell compression step. This does not prove Moise252 or the
full arbitrary-ambient/disconnected/nonseparating Moise264 contract. Do not
repeat accepted compression-component, target-separation or Betti arithmetic.

Current frozen independent queues are M304 through 41220900e, h e85a235df and
E3 c10b83586. S through c0 and F through71 are accepted. Existing active lanes
continue unchanged; deferred acceptance messages wait for their next completed
delivery. The task cadence remains hourly, without a new deadline or automatic
root rebuild, and existing two-private-checker resource limits remain in force.


### Actual end-straightening handoff, pending independent acceptance

S5b7117893 is frozen after F's accepted flat-sheet checkpoint. It supplies
actual disjoint supported level-preserving end adjustments and positive-width
open matching collars for the same original strip and complete Morse charts.
It does not yet supply a globally injective common cancellation domain or
complete cancellation. The next S round aligns the actual affine gauges and
proves global chart/source/image and overlap identities, then proceeds to
relative cubic coordinates or direct supported elimination in the same frame.
Its end isotopies do not claim to preserve the original field or every orbit
point. See integration section79 for frozen evidence and the completed-boundary
handoff. The current independent queue is M304 through412, h e85, E3 c10 and
S5b; earlier F71 and S throughc0 are accepted. All five lanes retain their
existing models, scopes and resource policy.

### Essential disk delivered; compatible compression ball is the next producer

M30406af1e40d is frozen after412, pending independent acceptance of the full
7a/96/412/06 chain. It produces the actual original K/L essential embedded
disk with explicit Moise252, exact boundary trace and old-boundary avoidance,
and retains the original shell in its annulus/compression consumer. The author
Lean delta is +230/-6; no independent mathematical acceptance is added yet.
The next dispatched round constructs the actual three-dimensional compression
ball, wall and caps around that same disk, choosing the annulus compatibly
and proving the exact trace equations before consuming existing separation
and strict Betti descent. See integration section80 for frozen identities and
scope. Other active lanes continue without mid-round messages.
