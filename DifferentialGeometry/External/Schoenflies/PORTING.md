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
mathematics, not an equal reduction in the remaining 3D smooth proof size.

Kimina consumer probes pass for smooth circle embeddings, a nonzero translation
whose extension must move the supplied point, exclusion of the empty Jordan
curve, and innermost selection from a singleton family. The probes import the
existing 3D entry point alongside the new planar interfaces.

Every new leaf is registered in the flat `DifferentialGeometry.lean` aggregate.
These are scoped source/REPL checks, not a completed aggregate build of the
unrelated full library. Normal IDE artifact preparation is in progress because
`lake --no-build setup-file` identified missing/stale dependency metadata.

The separation layer was committed and pushed as `ed97bb87e`. The complete
extension layer is the next verified checkpoint.
