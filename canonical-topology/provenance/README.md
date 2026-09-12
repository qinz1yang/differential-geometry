# Source provenance

The recovered source baseline is commit
`b45bfa009368c8f5f531e10f4f5280e90079d6ad`, originally available as
`refs/remotes/origin/codex/chapter35` in the controller's existing Git objects.
No source baseline was downloaded to prepare this checkpoint.

[SNAPSHOT.json](SNAPSHOT.json) records all 68 supplied module paths and hashes,
including their baseline hashes and the five new/changed leaves. The two new
files have a null baseline hash. Existing baseline hashes were independently
compared against the actual Git blobs. Every supplied leaf is byte-identical
to its current counterpart in the isolated Poincare workspace.

The portable `lakefile.toml` and `lake-manifest.json` are unchanged. The
`lean-toolchain` copy removes one trailing blank line while retaining its exact
version. The selected `Poincare.lean` is a checkpoint aggregate for the 68
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

## Historical authorities and acceptance boundary

[RECOVERED_AGENTS.md](RECOVERED_AGENTS.md) and
[RECOVERED_PROJECT_CONTEXT.md](RECOVERED_PROJECT_CONTEXT.md) preserve the original
authority records as provenance. Their historical Mac paths, branch instructions
and earlier release scope are not current instructions; the active package
[AGENTS.md](../AGENTS.md) records the current owner directions.

Source identity and import closure are packaging evidence. The main controller
verified fresh compilation of all 68 leaves and the root, public consumers,
package-wide stock declaration linters and standard-only transitive axioms on
2026-09-12. SNAPSHOT.json records the final request and evidence digests.
This does not certify the full canonical-topology suite or compatibility with
the missing frozen contract.
