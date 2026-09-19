# Moise 光滑化（拓扑三维流形 → 兼容光滑结构）阶段计划

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
inputs to 26.4 without assuming 26.4 or a compressing disk. Exact evidence
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
- 2026-09-19（H 车道 35.1 陈述与非空性修正）：`PolyhedralGraph.lean` 的
  `IsLocallyFiniteRegularNeighborhoodOf` 改用真正的二次 `derivedNeighborhood`，并以图像子复形、邻域像子复形和两组
  `IsGlueIso` 记录相邻有限层的单纯相容性；`ArcChainNeighborhood.lean` 的
  `exists_isLocallyFiniteRegularNeighborhoodOf_nonempty_arc` 在三维 PL 球内部边上给出 `N/K/U` 均非空的实际实例。
  `Moise351` 保留非紧、相对闭和逐点误差量词，经典证明仍未完成。三个模块私有检查 exit=0、零 warning；严格审计
  动态覆盖 40 个本模块声明，并单独审计 `LocallyFinitePieceTower.ofPiece`、`derivedNeighborhood` 及其面/空间/邻域接口、
  `secondDerived_isSubdivision`、`IsCombinatorialManifoldWithBoundary.derivedNeighborhood`、有限片流形桥、内部弧生产者、
  `arcComplexIn` 面接口、`chartPieceOfComplex` 与 `subset_interior_iff_mem_nhdsSet` 等 15 个复用声明。全部仅依赖
  `propext`、`Classical.choice`、`Quot.sound`，13 项适用 linter 全通过。
- 2026-09-19（H 车道 35.1 全局正则邻域修正）：复核原书书页 155、247–248 后确认，仅有逐层二次导出邻域与
  `IsGlueIso` 不足以保证无限并集为同一个正则邻域：后层新增图顶点会改变旧层重心投影，且没有相对邻域穷竭时逐层连续映射
  无法保证在并集上连续。`Topology/Homotopy/DeformationRetract.lean` 的
  `CompatibleStrongDeformationRetractSystem`，记录逐层强形变收缩、全对阶段相容性和下一层相对总并集的邻域性质；
  `toStrongDeformationRetract` 用最早出现层和 `continuous_of_cover_nhds` 实际粘出总并集到核心并集的强形变收缩。
  `IsLocallyFiniteRegularNeighborhoodOf.nonempty_strongDeformationRetract` / `strongDeformationRetract` 因而给出 `N ↘ K`。
  有限构造把 `derivedNeighborhoodStrongDeformationRetract` 经 `PLPieceIn.isClosedEmbedding` 搬到片像并取常值相容系统；
  内部非空弧实例与 `MoiseChain` 均重编通过。四模块聚焦检查 exit=0、零 warning；严格审计动态覆盖 69 个本模块声明及
  14 个直接复用声明，公理仅 `propext`、`Classical.choice`、`Quot.sound`，13 项适用 linter 全通过。35.1 本身仍开：
  非恒定生产者必须从单个局部有限直线三角剖分与相容对偶胞腔改造构造该系统，不能把全局收缩另作结论型假设。
- 2026-09-19（H 车道通用收缩接口归位）：`StrongDeformationRetract.homeomorphImage` / `embeddingImage`、
  `CompatibleStrongDeformationRetractSystem` 及其总并集连续性证明已从 PL 专用叶移入
  `Topology/Homotopy/DeformationRetract.lean`；三个集合辅助定义同时去掉无用的拓扑假设。原 PL 叶与根聚合 import 已删除，
  `PolyhedralGraph`、非空弧模型及 `MoiseChain` 签名不变。四模块私有检查 exit=0、零 warning；严格审计动态覆盖 88 个
  本模块声明与 14 个直接复用声明，公理仅 `propext`、`Classical.choice`、`Quot.sound`，13 项适用 linter 全通过。
  这只闭合自然归位；35.1 的非恒定几何生产者仍须从单个局部有限三角剖分推出相容性。
- 2026-09-19（H 车道导出邻域限制自然性）：`derivedNeighborhood_faces_mono` 与
  `derivedNeighborhoodBarycentricProjection_eq_of_restrict` 证明：环境有限子复形递增且图子复形在旧面上精确不变时，
  规范重心投影及其线性同伦在旧导出邻域上不变。`derivedNeighborhoodCompatibleStrongDeformationRetractSystem`
  再由面单调、精确限制和逐层 interior 缓冲实际生产相容强形变收缩系统，不把相容性作为输入。两模块私有检查
  exit=0、零 warning；严格审计 64 个本模块声明与 9 个复用声明，公理仅标准三公理，13 项适用 linter 全通过。
  现有 35.1 关系仍缺把此定理接到塔的条件：旧导出邻域未保证落在 `core i`，且后一层图未保证在像 core 上恰为旧图；
  单独的 `GImage`/`DImage IsGlueIso` 不能推出规范投影相容。下一步须修正该几何接口并给非恒定非紧实例。
- 2026-09-19（H 车道单一三角剖分接口修正）：`IsDerivedNeighborhoodExhaustion` 现直接记录固定欧氏实现中的单一局部有限
  复形 `J`、面集递增且穷尽 `J` 的有限环境层 `A i`、同一实现中的图层 `L i`、旧环境面上的精确限制、导出邻域的
  相对邻域穷尽，以及总并集到流形的一个嵌入。`IsLocallyFiniteRegularNeighborhoodOf` 不再含自由给定的相容 SDR，也不再
  使用两组彼此不足以约束重心投影的 `GImage`/`DImage IsGlueIso`。规范阶段收缩由
  `derivedNeighborhoodCompatibleStrongDeformationRetractSystem` 从上述几何数据推出，再搬到 `N ↘ K`。有限构造、内部弧模型与
  `MoiseChain` 的公开签名不变。四个私有模块检查均 exit=0、零诊断；严格审计覆盖 155 个模块声明与 20 个直接复用声明，
  公理仅标准三公理，13 项适用 linter 全通过。下一独立检查点是非恒定非紧实例；35.1 的对偶胞腔改造与逐点误差 PL 同胚仍未证明。
- 2026-09-19（H 车道非恒定非紧实例）：`noncompact_derivedNeighborhoodExhaustion_nat` 在
  `EuclideanSpace ℝ (Fin 1)` 中取一个自然数的拓扑嵌入，以全部像点的零维复形为单一局部有限 `J`，并令 `A i = L i`
  为前 `i+1` 个顶点的复形。证明内实际得到面集严格单调、有限层穷尽 `J.faces`、逐层导出邻域相对邻域性、总支撑到 `ℕ`
  的同胚及 core 等于全空间；结论同时给 `IsDerivedNeighborhoodExhaustion (n := 0) univ univ` 与目标非紧性。
  `PolyhedralGraph` 私有聚焦检查 exit=0、零诊断；严格审计动态覆盖六模块 160 个声明与 27 个直接复用声明，公理仅标准三公理，
  13 项适用 linter 全通过。这是新接口的实际 sanity check；35.1 的一维对偶胞腔改造与逐点误差 PL 同胚仍开。
- 2026-09-19（H 车道同环境 PL 正则邻域）：原书 155、247–248 页的文本与页面复核确认，35.1 的正则邻域必须来自 `U` 的同一个相对环境为 PL 的三角剖分；
  旧 `IsDerivedNeighborhoodExhaustion` 中的单个拓扑嵌入只足以搬运 SDR。新 `LocallyFinitePLPieceIn` 记录局部有限复形到 `U` 的嵌入参数化及正反图卡逐片仿射性；
  `IsPLDerivedNeighborhoodExhaustion` 将全部有限环境层、图层和导出邻域绑定到该单一实现，并证明忘却到纯拓扑穷尽及 `N ⊆ U`。`IsLocallyFiniteRegularNeighborhoodOf` 现消费这一加强层，
  `PLPieceIn.toLocallyFinite` 给出有限生产者，弧模型与 `Moise351` 公开签名不变。三个消费模块聚焦检查零诊断；严格审计 176 个模块声明加 28 个直接复用声明，仅标准三公理，13 项 linter 全过。
- 2026-09-19（H 车道非紧三维 PL 导出邻域模型）：`PolyhedralGraph.lean` 的
  `exists_noncompact_isPLDerivedNeighborhoodExhaustion_three_with_edge` 从一个含内部单边弧的有限组合 3-球出发，取整数方向彼此分离的仿射平移，并以对称有限区间形成非恒定环境层与图层。全体分量组成同一个局部有限欧氏复形，恒等映射给 `LocallyFinitePLPieceIn`；旗标的分量唯一性给导出邻域的逐分量面/空间公式和严格旧面限制，局部有限闭分量族的外部并之补集给下一层相对邻域。端点同时证明总导出邻域非紧、核心含非退化线段，并由规范相容穷竭得到全局强形变收缩。私有聚焦检查 exit=0、零诊断；严格审计六模块 196 项及 39 项直接复用声明，仅 `propext`、`Classical.choice`、`Quot.sound`，13 项 linter 全过。零维实例继续只作接口 sanity check；35.1 的实际对偶胞腔改造与逐点误差 PL 同胚仍未证明。
- 2026-09-19（H 车道 F4.3 顶点对偶胞腔球性）：`DualCellDecomposition.lean` 的
  `IsCombinatorialManifold.isPLBall_graphDualCell` 已证明有限组合 3-流形中图的每个 `graphDualCell` 是 PL 3-球。证明在粗顶点对偶球内把它分解为中心顶点与各关联边形心的对偶球；中心交集是 PL 2-球，不同关联边形心不可比较，故附加球两两不交，再用有限边界盘粘合。聚焦检查零诊断；严格审计模块 11 项与 19 项直接复用声明，只含标准三公理且 13 项 linter 全过。F4.3 与计划 R8 由此闭合；35.1 尚需逐边穿孔、环带嵌套、局部有限误差选择及逐胞腔逼近拼接。
- 2026-09-19（H 车道 35.1 有限刺穿层）：`DualCellPiercing.lean` 的
  `IsCombinatorialManifold.exists_graphDualCell_piercing` 将标准 2-单形的仿射内缩边界搬到实际 splitting disk 的相对内部，再用 `BoundaryInwardPush` 只固定该圆并内推相邻图双胞腔；所得像仍是包含于原胞腔的 PL 3-球，且与中心胞腔精确交于该圆。`exists_graphDualCell_piercings_of_trivalent_vertex` 对邻点恰由一个单射 `Fin 3` 枚举的真实三价顶点同时构造三条刺穿圆，并由不同 splitting disk 的不交性证明它们两两不交。没有结论型输入。聚焦检查零诊断；严格审计模块 12 项与 14 项直接复用声明，仅标准三公理，13 项 linter 全过。35.1 尚缺嵌套正则邻域及四个边界环带、局部有限误差选择和逐胞腔逼近拼接。
- 2026-09-19（H 车道 35.1 刺穿边界环带）：`NestedCircleBicollar.lean` 从球面圆的实际 PL 双领口生产任意指定相对邻域内的内外嵌套环带，用开集 `O` 显式证明内环带落在外环带的球面相对内部。`DualCellPiercingAnnuli.lean` 将其应用到实际中心 `graphDualCell` 边界和内推后邻胞腔的搬运边界，给出 Figure 35.1 的四条边界环带；三价端点同时产生三组数据并保留刺穿圆两两不交。聚焦检查零诊断；严格审计两模块 5 项新声明及 12 项关键复用声明，仅标准三公理，13 项 linter 全过。四环带仍未识别为同一对三维正则邻域 `T_e ⊂ Int S_e` 的截迹；这一公共实心环面对、局部有限误差选择与逐胞腔拼接仍开。
- 2026-09-19（H 车道 35.1 公共派生邻域）：`DerivedNeighborhoodRestriction.lean` 证明环境派生邻域与子复形的交精确等于子复形内的派生邻域。`CommonCircleDerivedNeighborhood.lean` 同时三角剖分公共核与两个紧多面体，在任意指定开集内生产环境派生邻域，并证明其两个截迹的精确等式和原环境中的相对邻域性。两模块私有检查零诊断；严格审计 3 项新声明和 10 项关键复用声明，仅 `propext`、`Classical.choice`、`Quot.sound`，13 项 linter 全过。公共正则邻域的组合层由此闭合，下一条记录继续完成环带分类与嵌套构造。
- 2026-09-19（H 车道 35.1 实际刺穿的嵌套公共环带邻域）：`CommonCircleNeighborhood.lean` 将公共环境细分、圆核、两个曲面子复形、全部面包含、相对邻域证书与两个精确截迹保存在同一谓词中，并用曲面圆邻域定理把两截迹都识别为标准 PL 环带；在第一个相对邻域所给开集中重做一次得到内外嵌套。`DualCellPiercingNeighborhoods.lean` 把它接到实际 `graphDualCell` 刺穿，保留改造邻胞腔、精确交圆等式和四个精确环带截迹。一般三价端点仍以精确邻点枚举为假设；`TrivalentDualCellNeighborhoodModel.lean` 在标准 4-单形边界及由同一顶点发出的三条边所生成的图子复形上证明该假设并构造三组真实实例。四模块私有检查零诊断；严格审计 13 项新声明和 20 项关键复用声明，仅标准三公理，13 项 linter 全过。未声称环境派生邻域为标准 PL 实心环面，因为尚无相应三维 PL 类型生产者；局部有限同步选择、受控逐胞腔修改和拼接仍开。
- 2026-09-19（H 车道 35.1 局部有限误差控制）：`LocallyFiniteErrorControl.lean` 在 `LocallyFinitePLPieceIn` 上从连续正逐点误差为每个紧单形选择正的统一下界，再用单形载体族的 point-finite 性同时选择所有顶点正尺度，使每个尺度严格小于所有关联面的阈值。这闭合书页 250 中局部有限性负责的纯数值选择，不把条件 (2)–(8) 的几何稳定性包装成假设结论。模块私有检查零诊断；严格审计 3 项新声明和 5 项关键复用声明，仅标准三公理，13 项 linter 全过。当前真实缺口是为各局部包含、分离、一般位置和有限交条件生产正稳定阈值；此外 `Moise341` 仍只是未证命题。
- 2026-09-19（H 车道 35.1 任意邻接族刺穿）：`DualCellPiercingNeighborhoods.lean` 将三价专用构造提升为自然的一般主定理 `IsCombinatorialManifold.exists_piercings_with_nested_common_neighborhoods`：对一个顶点的任意单射索引完整邻接族，同时生产逐边刺穿圆、改造邻球、PL 映射与两层嵌套公共环境派生邻域，并证明刺穿圆两两不交；原 `Fin 3` 定理成为直接推论。生产模块与实际三价模型消费端私有检查零诊断；严格审计模块全部 3 项声明和 2 项关键复用声明，仅标准三公理，13 项 linter 全过。未声称环境邻域两两不交或逐胞腔修改已相容，这两点仍受条件 (2)–(8) 的正稳定阈值缺口约束。
- 2026-09-19（H 车道 35.1 有限星的互不交嵌套公共邻域）：`IsCombinatorialManifold.exists_piercings_with_pairwise_disjoint_nested_common_neighborhoods` 对有限邻接族利用实际分裂盘的紧性与两两不交性，在指定开集内先取两两不交开加厚，再构造逐边外、内两层公共派生邻域；两层各自两两不交，并保留所有刺穿见证和精确环带截迹。实际三价模型已消费强端点，不是条件实例。两模块私有检查零诊断；严格审计 8 项模块声明和 7 项关键复用声明，仅标准三公理，13 项 linter 全过。现余跨局部有限穷竭的兼容修改与条件 (2)–(8) 的正稳定半径。
- 2026-09-19（H 车道 35.1 局部有限分裂盘支撑隔离）：`LocallyFiniteSplittingDisks.lean` 对同一个 `LocallyFinitePLPieceIn` 的所有边证明分裂盘逐个只有有限面，并证明其环境实现组成局部有限、两两不交的闭集族；`exists_locallyFinite_pairwise_disjoint_open_splittingDisk_neighborhoods` 用精确局部有限细化与 shrinking lemma，在任意指定公共开集内同时给出局部有限、两两不交的开邻域。`PolyhedralGraph.lean` 新导出的 `exists_noncompact_locallyFinite_simplicialComplex_three_with_edge` 和端点 `exists_noncompact_splittingDisk_neighborhood_family_three` 给出欧氏三维空间中含实际边的非紧非空模型。两模块私有检查零诊断；严格审计两模块 63 项非自动声明及 18 项直接复用声明，仅标准三公理，13 项 linter 全过。该层只闭合单一局部有限三角剖分中的开支撑隔离；现有分裂盘 PL 2-球定理仍需全局有限环境，跨层相容逐胞腔修改、条件 (2)–(8) 的正稳定半径、PL 实心环面分类与 `Moise351` 仍开。

- **Locally finite splitting-disk ballness (2026-09-19).**
  `LocallyFinitePLPieceIn.isPLBall_splittingDisk` now derives ballness for the exact splitting disk from finite local cofaces, the combinatorial face-link sphere, the upper-link radial PL homeomorphism, and the barycentric closed-star theorem, with no globally finite ambient complex and no ballness hypothesis.  A countable disjoint union of translated finite combinatorial PL three-spheres supplies a genuinely noncompact locally finite three-manifold with a real edge, and `exists_noncompact_locallyFinite_splittingDisk_isPLBall_model` verifies the endpoint there.  Three focused checks were clean; the strict audit covered 85 module declarations and 24 reused declarations with only the standard three axioms and all 13 linters.  Compatible cellwise modifications, stability radii, the solid-torus input, and `Moise351` remain open.
- **Locally finite separation API (2026-09-19).**
  `Topology/LocallyFiniteSeparation.lean` now provides the canonical metric-free separation theorem for locally finite pairwise-disjoint closed families in normal paracompact spaces.  Both the finite piercing construction and the locally finite splitting-disk construction consume it, so the former metric thickening proof and the latter private copy are gone.  The new leaf is registered in the root aggregate; three focused checks were clean, and the strict audit covered 17 module declarations plus 10 reused declarations with only the standard three axioms and all 13 linters.
- **Finite piercing-neighborhood perturbation stability (2026-09-19).**
  The metric theorem now lives at its natural home as `Topology.Compactness.exists_perturbation_radius_preserving_containment_pairwise_disjoint`; it assumes only finite compact outer sets, open containment, inner-to-outer inclusions, and pairwise disjointness.  `DualCellPiercingStability.lean` retains the derived-neighborhood result as a direct corollary.  The standard 4-simplex-boundary trivalent graph supplies an actual nonempty consumer with `U = Metric.thickening 1 K.space`.
- **Supported nonidentity perturbation of piercing neighborhoods (2026-09-19).**
  `exists_isPLHomeomorphOn_moves_point_dist_lt` constructs an actual ambient PL self-homeomorphism moving a prescribed point, fixed outside an `ε/4` ball and globally `ε`-close to the identity.  `exists_trivalent_graphDualCell_supported_perturbation_model` chooses a point on an actual piercing circle and consumes the previously produced `δ`; transformed outer neighborhoods remain in `U`, both transformed layers stay pairwise disjoint, open nesting transports exactly, and all four surface intersections retain their finite common-subdivision and intrinsic derived-neighborhood witnesses.  The new leaf is root-registered; four focused checks were clean, and the joint strict audit covered 11 target declarations plus 12 reused declarations with only the standard three axioms and all 13 linters.  The transformed sets are not yet proved to be derived neighborhoods in one compatible finite triangulation, and the move is not graph-relative; Conditions (3)--(8), cross-stage compatibility, the solid-torus input, and `Moise351` remain open.
- **Graph-relative supported perturbation of piercing neighborhoods (2026-09-19).**
  `exists_isPLHomeomorphOn_moves_point_dist_lt_eqOn` constructs the relative ambient move for a closed protected set inside an allowed open support.  In the actual trivalent consumer, a point of the first piercing circle is chosen away from the incident edge centroid, and `splittingDisk_space_inter` proves that it is outside the original graph.  Hence `exists_trivalent_graphDualCell_relative_supported_perturbation_model` has a positive support ball in `U \ L.space`, fixes all of `L.space` and `Uᶜ`, moves that point, stays below the stability radius, and retains transformed containment, pairwise disjointness, open nesting, and all four image-derived-neighborhood trace certificates.  Both changed modules checked cleanly; the strict audit covered all 6 target declarations and 13 critical reused declarations with only the standard three axioms and all 13 linters.  The remaining representation obligation is a finite triangulation simultaneously compatible with the graph, both surfaces, and the modification, followed by a proof that the modified sets are canonical derived neighborhoods there.  Arbitrary PL homeomorphisms do not preserve a chosen barycentric-derived construction.  Conditions (3)--(8), cross-stage compatibility, the solid-torus input, and `Moise351` remain open.
- **Original-carrier PL perturbation of piercing neighborhoods (2026-09-19).**
  `exists_isPL_homeomorph_moves_point_dist_lt_eqOn` conjugates a supported Euclidean point move through an actual PL chart of any positive-dimensional metrized PL manifold.  It produces a PL self-homeomorphism of the same carrier, with PL inverse, compact support inside the allowed open set minus the protected closed set, exact pointwise fixing, a moved prescribed point, and the requested global displacement bound.  `exists_trivalent_graphDualCell_carrier_supported_perturbation_model` applies it to the original `K.space` of the real trivalent model.  The move fixes the graph preimage and preserves the original carrier; its auxiliary ambient-valued extension is proved only to be a bijection preserving `K.space`, fixing `L.space` and `Uᶜ`, and retaining containment, pairwise disjointness, and intrinsic open nesting.  It is deliberately not advertised as an ambient continuous or PL map.  Both target modules checked cleanly; the strict audit covered all 4 target declarations and 14 critical reused declarations with only the standard three axioms and all 13 linters.  The new leaf is root-registered.  This repairs the former `h '' K.space` replacement.  The remaining exact gap is a finite triangulation compatible with the graph, both boundary surfaces, and this carrier self-homeomorphism, together with an affine-on-faces proof identifying the modified neighborhoods as canonical derived neighborhoods.  An arbitrary PL map or later unrelated refinement does not preserve the old barycentric-derived set.
- **Compatible triangulation of intrinsic PL homeomorphisms (2026-09-19).**
  `PLPieceIn.isPLHomeomorphOn_conjugate` and `PLPieceIn.map_conjugate_eqOn` give the exact coordinate representative of an intrinsic PL self-homeomorphism on a finite piece.  `PLPieceIn.exists_compatible_isGlueIso_of_homeomorph` simultaneously makes any finite family of polyhedra into source subcomplexes, simplicializes that representative on finite source and target subdivisions, and transports every named source subcomplex to a target subcomplex whose carrier is exactly its image.  The focused check was clean; the strict audit covered all 3 target declarations plus 13 critical reused declarations with only the standard three axioms and all 13 linters.  Thus the common finite triangulation and affine-on-faces layer is a proved reusable producer.  The trivalent consumer still must package the graph, both surface families, and inner/outer neighborhoods as the finite input family; exact transport of the canonical barycentric-derived construction under the resulting `IsGlueIso` remains separate and is not inferred from arbitrary subdivision invariance.
- **Actual trivalent compatible triangulation (2026-09-19).**
  `TrivalentPiercingSetIndex` and `trivalentPiercingSet` package the graph, three piercing circles, central surface, three branch surfaces, and three inner/outer neighborhood pairs into one finite family.  `isPolyhedron_trivalentPiercingSet` and `trivalentPiercingSet_subset` derive all fourteen polyhedron and carrier facts from the existing common-annular-derived-neighborhood witnesses.  `exists_trivalent_graphDualCell_compatible_triangulation_model` applies the now arbitrary-finite-dimensional `PLPieceIn.exists_compatible_isGlueIso_of_homeomorph` to the actual graph-fixed nonidentity carrier perturbation and returns one pair of finite source/target subdivisions with exact source and image subcomplexes for every family member.  Both modules checked cleanly; the joint strict audit covered all 20 non-automatic declarations plus 15 critical reused declarations with only the standard three axioms and all 13 linters.  Exact `IsGlueIso` transport of canonical barycentric derived neighborhoods remains the representation gap; unrelated later subdivisions are still not asserted to preserve them.

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
