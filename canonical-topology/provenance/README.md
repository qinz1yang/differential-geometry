# Source provenance

The recovered source baseline is commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, originally available as
`refs/remotes/origin/codex/chapter35` in the controller's existing Git objects.
No source baseline was downloaded to prepare this checkpoint.

[SNAPSHOT.json](SNAPSHOT.json) records all 88 supplied module paths and hashes,
including their baseline hashes and the seven new/changed leaves. The three new
files have a null baseline hash. Existing baseline hashes were independently
compared against the actual Git blobs. Every supplied leaf is byte-identical
to its current counterpart in the isolated Poincare workspace.

The portable `lakefile.toml` and `lake-manifest.json` are unchanged. The
`lean-toolchain` copy removes one trailing blank line while retaining its exact
version. The selected `Poincare.lean` is a checkpoint aggregate for the 88
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
