# Planar Jordan separation and crosscuts

Source: https://github.com/alonamaloh/schoenflies-lean
Pinned commit: `05a43d29cde026618777db3d4e4316204ccca237`.
Author: Álvaro Begué. License: Apache-2.0.
Original LICENSE, README.md and formalization.yaml are preserved unchanged.
Their project configuration and completion status describe upstream.

This checkpoint vendors the 76-module transitive dependency closure of
`Schoenflies.jordan_curve_theorem` and the crosscut results in `JordanClosed.lean`:
37,857 upstream physical Lean lines. Internal module imports are relocated;
original namespaces and documentation are preserved. See MODIFICATIONS.md.
The log also records compatibility work for the ambient-extension port in progress.

All 76 module sources passed checks in the matching Lean 4.33.1 REPL with the
project's source linters, declaration linters unusedArguments/simpNF/synTaut,
and transitive standard-axiom checks over every new declaration. The installed
version has no defLemma linter. No new axiom, sorry, linter suppression or proof
budget override was added. Normal IDE build metadata is still being prepared;
this is not a completed aggregate Lake build.

Import `DifferentialGeometry.Topology.JordanSeparation` for the local interfaces:
`Topology.IsEmbedding.isJordanCurve_range` connects the standard Euclidean circle
to the Jordan predicate; `Schoenflies.exists_innermost_jordan_curve` supplies
Chapter 42's innermost finite-family choice. Both pass the same REPL checks.

The ambient Jordan--Schoenflies extension is the next dependency-closed layer.
Smooth planar filling and the 3D smooth Schoenflies theorem remain unproved.
