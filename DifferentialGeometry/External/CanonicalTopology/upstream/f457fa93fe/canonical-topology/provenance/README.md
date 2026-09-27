# Source provenance

The recovered source baseline is commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, originally available as
`refs/remotes/origin/codex/chapter35` in the controller's existing Git objects.
No source baseline was downloaded to prepare this checkpoint.

[SNAPSHOT.json](SNAPSHOT.json) records all 103 supplied module paths and hashes,
including their baseline hashes and the nineteen new/changed leaves. The fourteen new
files have a null baseline hash. Existing baseline hashes were independently
compared against the actual Git blobs. Every supplied leaf is byte-identical
to its current counterpart in the isolated Poincare workspace.

The portable `lakefile.toml` and `lake-manifest.json` are unchanged. The
`lean-toolchain` copy removes one trailing blank line while retaining its exact
version. The selected `Poincare.lean` is a checkpoint aggregate for the 103
supplied leaves; it does not overwrite the full recovered project's aggregate.
Original/current hashes for these files are recorded separately.

## Adapted derivative homotopy

`Poincare/Analysis/LocalDerivativeHomotopy.lean` adapts the explicit subtype
homotopy from [plby/HopfProblem, Solution.lean, lines 62156--62228](https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/Solution.lean#L62156),
commit `9ac8a456b526527837d7082ff775213ca8bc9809`.
The source is released under [Apache-2.0 at that revision](https://github.com/plby/HopfProblem/blob/9ac8a456b526527837d7082ff775213ca8bc9809/LICENSE);
[APACHE-2.0.txt](APACHE-2.0.txt) supplies the license text.

The local adaptation uses the separately proved derivative estimate, a whole
punctured ball, and explicit continuous endpoint maps and interpolation
equations. It replaces the source's sphere/`BoundaryData` interface and uses the
pinned Mathlib APIs. Its source file carries the attribution and change notice.

The pinned source header and selected block were inspected directly. The block
contains no separate copyright/author notice. The repository's complete root
tree contains `LICENSE` and no `NOTICE` file. The header separately attributes
complex-analysis, sphere-connectivity/van-Kampen, and final S6-statement material
from other sections; those sections are outside this adaptation.

The other additions reuse the recovered Poincare singular and relative homology
objects and pinned Mathlib. No DifferentialGeometry source is vendored and no
dependency revision changes. This attribution record does not assert a new
license for the remaining recovered project sources.

## Linear determinant-sign extension

The 74 previously supplied sources are unchanged. Thirteen further homology
leaves are copied byte for byte from the same recovered baseline, including
their original documentation. `Poincare/Topology/Homology/LocalLinearMaps.lean`
is new original code using those Poincare and pinned Mathlib APIs. It exports
only the intrinsic linear-equivalence determinant-sign theorem and keeps the
reflection, sphere and matrix proof machinery private. Its source hash is
`d9284f07e88a77db3a9f90fa22291b8c2c6a5d3c7036f30e26865afe8ec0459d`.

The original isolated module and imported consumers passed request
`1789235551579974740-topology-d57a1cb3` in Slurm 13781140. SNAPSHOT.json records
that result separately from portable package acceptance. All 74 existing Lean sources, dependency
pins, installations and path manifests are preserved.

## Historical authorities and acceptance boundary

[RECOVERED_AGENTS.md](RECOVERED_AGENTS.md) and
[RECOVERED_PROJECT_CONTEXT.md](RECOVERED_PROJECT_CONTEXT.md) preserve the original
authority records as provenance. Their historical Mac paths, branch instructions
and earlier release scope are not current instructions; the active package
[AGENTS.md](../AGENTS.md) records the current owner directions.

Source identity and import closure are packaging evidence. The previous
68-module checkpoint passed fresh leaves/root, public consumers, package-wide
stock linters and standard-only transitive axioms on 2026-09-12. The expanded
74-module snapshot also passed its fresh affected-leaf/root gate, all-package
and consumer declaration linters, 12 public exports, four nonidentity consumers
and a nonzero degree-zero class consumer. SNAPSHOT.json preserves both verified checkpoints and the original linear-sign
module evidence. The expanded 88-module portable snapshot passed request
`1789236250289124336-topology_checkpoint-db7e7dbe`: all 14 added leaves and the
root freshly compiled, followed by all-package/current-consumer stock linters
and standard-only axioms, 13 public exports and 22 signature/axiom pairs. All
93 guarded inputs matched the final source. The unchanged 74 leaves retain
their earlier compilation evidence; this run did not freshly rebuild them.
This does not certify the full canonical-topology suite or compatibility with
the missing frozen contract.

## Closed-ball local classes

`Poincare/Topology/Homology/LocalBallHomology.lean` was introduced as a 399-line module
using the existing singular/relative homology and pinned Mathlib APIs. Its four
public results retain arbitrary normed real spaces, natural degrees, centers
and nonnegative radii, including zero and boundary cases. The actual complement
inclusion is a homotopy equivalence; the resulting center restriction is an
isomorphism. A translation homotopy proves all normalized restrictions of one
unique class agree. The 22 construction helpers are private.

The 89 previous leaves are unchanged. Portable request
`1789247905874477991-topology_checkpoint-baeeac80` freshly compiled the new
leaf and root, then passed all-package/consumer stock linters, standard-only
axioms, 21 public exports and 40 exact signature/axiom pairs. All 102 source
and configuration guards matched. Previous validation records are preserved
in SNAPSHOT.json; the missing frozen handoff and full topology suite remain open.

## Unique compact chart classes

`Poincare/Topology/Homology/LocalCompactHomology.lean` is a new 481-line module
with four public exports and twelve private construction helpers. It combines
the existing actual open excision, chart maps and closed-ball class theorem.
It retains the chart isomorphism's actual excision and point-restriction laws,
then constructs a compact neighborhood and a unique normalized relative class.
No differential-geometry source, global fundamental class or deferred input
is introduced.

`EuclideanLocalTop`, `SphereTopHomology` and `SphereHomologyVanishing` are
unchanged copies of the recovered baseline, including their documentation.
Their actual Git blobs were compared before copying. They support the new
nonzero three-dimensional consumer. All 90 previous leaves remain unchanged.

The four added leaves and root compiled silently in request
`1789250063643581109-topology_checkpoint-2f2e02e3`. The final replay
`1789250353396415278-topology_checkpoint-c6197cda` passes all-package/current
stock linters, standard-only axioms, 25 public exports and 48 exact readback
pairs. Its only intervening repair removed duplicate universe declarations
from the combined consumer harness. All 94 source files match the successful
build, and all 109 final input guards match. SNAPSHOT.json preserves both
the artifact-build identity and the final replay evidence.

## Oriented compact neighborhood classes

`LocalOrientation` now also constructs a compact neighborhood and unique
relative class normalized consistently in all charts with compatible actual
tangent orientations. Its old 260 lines are preserved; only one import and
one theorem are added. The class and chart maps are the
existing Poincare objects, and no global fundamental-class input is assumed.
The other 93 leaves and 94-module aggregate are unchanged.

Portable request `1789251985955893192-topology_checkpoint-9c57dab9` freshly
compiled the changed leaf and root, then passed all-package/current-consumer
stock linters, standard-only axioms, 26 public exports and 51 exact readback
pairs. All 48 previous readback pairs are identical, and all 115 guards match.
The nonzero and Euclidean3 consumers passed. SNAPSHOT.json preserves the
previous compact-chart checkpoint and the original imported-neighborhood gate.

## Bounded star-convex complements

`Topology/Homotopy/StarConvexComplement.lean` contains the generalized radial
expansion formerly used only for a centered closed ball. Its public homotopy
equivalence uses Mathlib's actual `ContinuousMap.inclusion`; the lower topology
module has no homology dependency. `Topology/Homology/LocalStarConvex.lean`
applies the existing pair short exact sequences and Mathlib's homology functor
to identify the original relative restriction with an isomorphism.

The two new leaves contain 134 and 56 lines. `LocalBallHomology` now contains
269 lines, with its final 241 lines and all four public declaration bodies
preserved verbatim. The old radial construction is replaced, not duplicated.
The other 93 previously supplied leaves are unchanged. The expanded aggregate
contains 96 leaves; dependency configuration and existing attribution are
unchanged. The new original proofs use pinned Mathlib and Poincare APIs.

Final portable request `1789254131971909628-topology_checkpoint-8c2ff12b`
passed in Slurm 13781140 in 235.92 seconds. The two new leaves, refactored
`LocalBallHomology`, affected `LocalCompactHomology` and `LocalOrientation`,
and `Poincare` freshly compiled without diagnostics in 2:54.59. All 122
source/configuration/harness guards and 61 signature/axiom pairs passed.
All 51 previous pairs and the ten new public/consumer pairs match their earlier
readbacks byte for byte. All-package/current-consumer stock linters and
standard-only transitive axioms passed. The 91 unchanged leaves not rebuilt
in this run retain their earlier compilation evidence.

## Local and convex-support vanishing

The checkpoint adds `RelativeVanishing` (25 lines), `EuclideanLocalVanishing`
(135 lines) and `CompactVanishing` (46 lines). `EuclideanLocalVanishing` extends
the recovered baseline while preserving its four prior public statements,
proof bodies and documentation. The high-degree proof reuses the existing
dimension-at-least-two theorem; the new rank-zero/one cases use the original
relative sequence and sphere computations. Arbitrary real norms are handled
by an actual continuous linear equivalence to Euclidean space.

The new relative-universe and convex-support modules are original proofs over
pinned Poincare and Mathlib APIs. No DifferentialGeometry source, dependency
change or deferred input is introduced. The star-convex primary derives center
membership from nonemptiness internally and handles the empty set separately.
All 96 previously supplied leaves remain unchanged.

Original imported request `1789256262590000029-topology-6245d09b` freshly
compiled all three leaves and passed 137 guards and 16 signature/axiom pairs.
Portable request `1789256733392947972-topology_checkpoint-e20ea2ab` freshly
compiled those leaves and root without diagnostics in 1:50.75, maximum RSS
1923004 KiB. Its full gate passed in 172.69 seconds with 131 guards and 77
signature/axiom pairs. The 61 previous readbacks are identical; the 16 new
readbacks match the original gate up to `Set.univ`/`Module.finrank` qualification.
Stock declaration linters and standard-only transitive axioms pass. Earlier
validation records remain in SNAPSHOT.json; this is a foundations checkpoint,
and the full topology suite remains incomplete.

## Relative Mayer–Vietoris classes

`RelativeMayerVietoris.lean` is a new 815-line original development over the
existing Poincare small-chain/relative complexes and Mathlib homology sequence.
Its seven checked child blocks retain their exact lexical scopes and proof
bodies, apart from five public visibility changes, the `exists_unique` rename,
and using the public relative-universe vanishing theorem in the disjoint case.
Five natural results are public; 38 quotient/comparison/biproduct mechanics
remain private. No external source is copied into this leaf.

The primary constructs a matching intersection class for actual open-subspace
relative homology in every natural degree. Uniqueness explicitly requires
vanishing of the next-degree union-relative group. Closed-support gluing is a
corollary; disjoint supports require no agreement hypothesis. All maps are the
original Poincare relative maps. No fundamental class or point detection is
assumed. Existing licenses, source bodies and dependency pins are unchanged.

Full-source request `1789256791259413253-topology-6847705b` passed 107 guards
and 47 signature/axiom pairs. Original imported request
`1789257091124590712-topology-ee641796` freshly compiled the leaf and reproduced
the five public and four consumer readbacks exactly. Portable request
`1789257537165329093-topology_checkpoint-6a6afc66` freshly compiled the leaf
and root in 1:12.59, maximum RSS 1778292 KiB, then passed 138 guards and all
86 signature/axiom pairs. All 77 previous pairs and nine new original pairs
match byte for byte. All 100 portable/original sources match; the 99 prior
leaves remain unchanged. SNAPSHOT.json preserves the earlier build records.

## Compact support and manifold point restrictions

`CompactSupport` contains original proofs giving a finite compact carrier for
the same singular chain, extension of relative classes to compact neighborhoods,
and local zero restriction on a produced compact neighborhood intersection.
`CompactVanishing` now proves vanishing for arbitrary compact subsets of a
finite-dimensional real normed space. These use the original chain quotient,
the published local vanishing and actual Mayer–Vietoris engines.

`ManifoldCompactHomology` is new original code transporting compact vanishing
through actual chart isomorphisms and finite compact chart covers. It then
uses the local-zero theorem and native compact induction for point detection,
equality, and existence of a nonzero local restriction. Shared construction
mechanics remain private; five additional natural results are public across
this checkpoint's two edited leaves. No external source is copied, no
DifferentialGeometry source is vendored, and no dependency pin changes.

The original source gate237fc83e and imported gate4432c7fe passed. The latter
freshly compiled four required leaves in 1:54.88, maximum RSS 1922364 KiB,
then checked 150 guards and thirteen exact public/consumer pairs. Those pairs
match the full-source readbacks byte for byte.

Portable request `1789261428531126275-topology_checkpoint-fa830b31` freshly
compiled CompactSupport, CompactVanishing, ManifoldCompactHomology and root
in 2:26.11, maximum RSS 1928476 KiB, with zero diagnostics. Its complete gate
passed in 211.17 seconds with 199 guards and 106 signature/axiom pairs.
All 95 previous pairs are identical; the eleven new pairs match the original
imported gate up to Module.finrank/Set.Ioo qualification and formatting.
All 102 original/portable source pairs match. The other 100 prior leaves are
unchanged. Stock linters and standard-only axioms pass; earlier validation
records are preserved in SNAPSHOT.json. This does not close the full topology
suite or replace the missing frozen contract.

## Absolute-to-relative-empty comparison

`RelativeEmpty.lean` contains 51 lines of original code over the actual
Poincare chain complexes and pinned Mathlib cokernel/homology APIs. Two
private helpers establish the zero empty-subspace inclusion and bijectivity
of its actual quotient homology map. The two public declarations give a
linear equivalence and identify its forward map. No source is copied from
another project, and all previous 102 leaves and dependency pins are unchanged.

Original imported request `1789262707782850547-topology-b3b344aa` freshly
compiled the leaf in 0:28.22, maximum RSS 1546112 KiB, and passed five exact
public/consumer pairs. Portable artifact request
`1789262781992230755-topology_checkpoint-e5804880` freshly compiled the leaf
and root in 1:18.48, maximum RSS 1778200 KiB. Its later combined harness
failed on a duplicate universe declaration; production compilation was silent.
Final request `1789264345451073915-topology_checkpoint-f04d0bd9` changed only
that scratch scope and passed in 91.29 seconds, with a cached root build,
206 guards and 111 exact pairs. All 106 prior pairs are identical, and the
five added pairs match the original imported gate byte for byte. Stock
linters and standard-only transitive axioms pass. SNAPSHOT.json preserves
both the fresh artifact identity and the final successful gate.

## Signed manifold chart transition

`LocalOrientation` now exposes the actual determinant-sign relation between
two normalized manifold chart maps. Its previous oriented equality retains
its exact public statement and consumes this common engine; the compact
oriented-neighborhood theorem and proof remain unchanged. No source or
installation was downloaded for this extension.

The original source gate 07e84189 and imported gate 9989c94d pass. Final
portable gate 27c4be25 passes 212 guards and 115 signature/axiom pairs,
including all 111 previous pairs unchanged. The changed leaf and root freshly
compiled in 0b7eb007; the final replay changes only a duplicate universe in the
scratch consumer. All 102 other leaves are unchanged. SNAPSHOT.json preserves
the preceding relative-empty validation and records this checkpoint separately.

## Compact gluing and global generators

The added ManifoldCompactHomology block and new ManifoldFundamentalClass are
original proofs over the pinned Poincare/Mathlib objects. They reuse actual
relative Mayer–Vietoris gluing, compact point detection, local-zero neighborhoods,
and the actual absolute-to-relative-empty equivalence. A locally realized
family yields a unique global class; local generator laws plus connectedness
yield the actual global generator and point-restriction isomorphisms. Shared
identity-map naturality and local-vanishing mechanics remain private.
No external code, dependency revision or existing public signature changes.

Source request 135c6250 passed in 41.54s with 152 guards and 19 pairs. Original
imported cb09d399 passed in 104.32s with 152 guards and 9 pairs, after fresh
two-leaf compilation in 1:10.12, RSS 1920460 KiB. All nine imported pairs are
byte-identical to source. Portable 2584f507 passed in 159.33s with 222 guards
and 120 pairs. Changed ManifoldCompactHomology, new ManifoldFundamentalClass
and root freshly compiled in 1:32.34, RSS 1937172 KiB, with zero diagnostics.
All 115 previous pairs and 102 unchanged leaves are preserved. The new nonzero rank-zero consumer has actual
coordinate one. Stock declaration linters and standard-only axioms pass.
SNAPSHOT.json preserves the preceding signed-chart gate separately.

The local family is honest prerequisite data, not a completed tangent-orientation
producer. The full topology suite and missing frozen contract remain unresolved.

## Relative cochains and their exact sequence

`Poincare/Topology/Homology/RelativeCochains.lean` is new original development
over the recovered `CochainMaps`, `CarrierRestriction` and the pinned Mathlib
kernel, short-exact-sequence and homology-sequence APIs. It preserves the
original singular cochains, integral coefficients, chains and pair maps.
Its 25 public declarations expose the actual kernel inclusion, pullbacks,
cohomology maps and connecting map, with evaluation and naturality equations.
Three degreewise chain-retraction helpers remain private. They extend cochains
by the actual singular-simplex basis and are not claimed to commute with the
boundary operator. No competing cochain model or external source is introduced.

Source request `1789302544298781532-topology-306577bf` passed 50 guards and
30 signature/axiom pairs. The original imported check
`1789302721767496711-topology-5cffaa78` passed 52 guards and 27 pairs after a
fresh leaf build. Final portable request
`1789303157293002715-topology_checkpoint-d51aac36` passed 230 guards and
147 pairs, including all 120 previous pairs unchanged. New leaf and root
compiled silently; strict declaration linters and standard-only axiom guards
passed on that same snapshot. The snapshot retains the previous 104-module
validation separately. All 104 earlier sources remain byte-identical.
