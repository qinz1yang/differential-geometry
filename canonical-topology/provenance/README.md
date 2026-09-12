# Source provenance

The recovered source baseline is commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, originally available as
`refs/remotes/origin/codex/chapter35` in the controller's existing Git objects.
No source baseline was downloaded to prepare this checkpoint.

[SNAPSHOT.json](SNAPSHOT.json) records all 94 supplied module paths and hashes,
including their baseline hashes and the ten new/changed leaves. The six new
files have a null baseline hash. Existing baseline hashes were independently
compared against the actual Git blobs. Every supplied leaf is byte-identical
to its current counterpart in the isolated Poincare workspace.

The portable `lakefile.toml` and `lake-manifest.json` are unchanged. The
`lean-toolchain` copy removes one trailing blank line while retaining its exact
version. The selected `Poincare.lean` is a checkpoint aggregate for the 94
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

`Poincare/Topology/Homology/LocalBallHomology.lean` is a new 399-line module
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
