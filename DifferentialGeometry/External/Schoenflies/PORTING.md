# Planar Jordan--Schoenflies dependency

Upstream: <https://github.com/alonamaloh/schoenflies-lean>

Pinned commit: `05a43d29cde026618777db3d4e4316204ccca237`.
Author: Alvaro Begue (see the original Unicode attribution in each source file).
License: Apache-2.0; the original `LICENSE`, `README.md`, and
`formalization.yaml` are retained without modification. Their build instructions
and status describe the upstream project, not this port.

This directory contains the 128-module transitive dependency closure of
`Schoenflies.jordan_schoenflies_of_homeomorph`. The original `Schoenflies`
namespace and module subdivision are retained. Imports use the prefix
`DifferentialGeometry.External.Schoenflies` so the code uses this project's
installed Lean/Mathlib 4.33.1 and needs no separate dependency checkout.

The upstream `Compose.lean` and `InitialReverseTransfer.lean` are outside that
closure and are omitted. The Comparator challenge, auxiliary project build
configuration, and generated artifacts are not vendored. In particular, the
Comparator challenge's intentional `sorry` is not part of this library.

The useful public entry points are:

- `JordanClosed.lean`: the Jordan curve theorem, connectivity of arc complements,
  and polygonal crosscut separation with exact component and boundary equations.
- `JordanSchoenflies.lean`: extension of homeomorphisms between Jordan curves
  to ambient homeomorphisms of the plane, including closed-interior extension.

These are topological results in `EuclideanSpace ℝ (Fin 2)`. They do not assert
smoothness, three-dimensional separation, smooth ball filling, or ambient
diffeomorphism/isotopy results. The local smooth Schoenflies plan records their
consumers and the remaining smooth prerequisites.

All local source changes are described in `MODIFICATIONS.md`.

## Project interfaces

Use precise imports from the existing Lean project:

```lean
import DifferentialGeometry.Topology.JordanSeparation
import DifferentialGeometry.Topology.JordanSchoenflies
```

`Topology.IsEmbedding.isJordanCurve_range` in `Topology/JordanCurve.lean`
converts an embedding of `Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1`
into the upstream Jordan-curve predicate. It uses the actual circle
parametrization and preserves the embedding's image.

`Topology.IsEmbedding.jordan_schoenflies` gives an ambient homeomorphism
whose restriction to that circle is the supplied embedding, pointwise.
A smooth embedding can provide its `.isEmbedding` field; the returned
homeomorphism still has only topological regularity.

`Schoenflies.exists_innermost_jordan_curve` chooses a curve in a nonempty
finite family of pairwise disjoint Jordan curves whose bounded interior
misses every curve in the family. This is the topological content of
Chapter 42's innermost-circle lemma. Smooth disk fillings remain a separate
obligation.

## Verification and size

All 128 vendor modules and all three local interfaces pass exact-source checks
with the matching Lean 4.33.1 REPL, the project source linters, and the three
available declaration linters (`unusedArguments`, `simpNF`, `synTaut`).
`defLemma` is not available in this Mathlib version. Per-declaration transitive
axiom checks permit only `propext`, `Classical.choice`, and `Quot.sound`.
No source proof debt, budget overrides, or linter suppressions were added.

The checked closure represents **77,154 upstream physical Lean lines**, or
**50,665 nonblank noncomment code lines**, in 128 modules. This counts imported
mathematics. All of it is available as reusable dependencies; downstream smooth
proofs can consume the topological theorem without rewriting those dependencies.
Beyond import-prefix rewrites and modification notices, the port changes 204
added and 207 removed source lines across 56 files. The compatibility repairs
are small relative to the imported development.

A separate geometric bridge is still needed to obtain a smooth disk with its
given smooth structure. The active plan now calls for testing disk smoothing
before committing to a separate polygon-triangulation construction. Its old
40,000-90,000-line forecast has been withdrawn as a reliable current estimate:
that forecast did not budget for reproducing this whole topological library,
so subtracting its size would compare different proof routes.

Kimina consumer probes pass for smooth circle embeddings, a nonzero translation
whose extension must move the supplied point, exclusion of the empty Jordan
curve, and innermost selection from a singleton family. The probes import the
existing 3D entry point alongside the new planar interfaces.

Every new leaf is registered in the flat `DifferentialGeometry.lean` aggregate.
These are scoped source/REPL checks, not a completed aggregate build of the
unrelated full library. Normal IDE artifacts for all 131 new leaves are now
prepared. The initial `lake --no-build setup-file` check identified missing or
stale dependency metadata; the permitted artifact repair used one
`LEAN_NUM_THREADS=1 lake --no-cache --iofail build +MODULE:leanArts` at a time.
All 131 targets completed without diagnostics. Subsequent no-build editor
setup checks pass for `JordanCurve.lean`, `JordanSeparation.lean`, and
`JordanSchoenflies.lean`.

Against those final artifacts, the matching REPL rechecked all three declaration
linters and transitive axioms across the whole vendor package and the three
local modules. Exact signatures and axiom closures were read back for the
Jordan theorem, crosscut theorem, both extension engines, the ambient-extension
headline, and the three local headlines. The Kimina consumer probes were
replayed successfully with no diagnostics. All source hashes match the checked
snapshot, and `git diff --check` passes. The task Kimina server and its REPL
workers have been stopped; no caffeinate process remains.

Acceptance: **Accepted for the planar port and project interfaces**. This does
not establish the 3D smooth Schoenflies theorem.

The separation layer was committed and pushed as `ed97bb87e`. The complete
extension layer was committed and pushed as `392dcfd56` on `origin/ayush`.
