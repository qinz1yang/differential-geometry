# Planar arc disk neighborhoods

## Source and license

The square-chain construction in
`DifferentialGeometry/Topology/PlanarJordan/ArcDiskNeighborhood.lean` adapts the
proof of `Schoenflies.exists_face_of_notMem_arc` in `Schoenflies/ArcComplement.lean`
from [alonamaloh/schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean),
upstream commit `05a43d29cde026618777db3d4e4316204ccca237`.

Copyright (c) 2026 Alvaro Begue. All rights reserved.
Original author: Álvaro Begué.
Released under the Apache License, Version 2.0. The complete license is retained
at [LICENSE](../../DifferentialGeometry/External/Schoenflies/LICENSE), with the
upstream record and compatibility history at
[MODIFICATIONS.md](../../DifferentialGeometry/External/Schoenflies/MODIFICATIONS.md).

## Native adaptation, 2026-09-16

- Extract the coarse/fine partition and square-chain geometry into a private
  helper. Preserve the nonadjacent-subarc separation and consecutive-pair bounds.
- Replace the original two fixed points off the arc with a uniform statement for
  every point outside a prescribed thickening of the arc.
- Retain strict open-square coverage to show the arc misses the closure of the
  unbounded face, not just the face itself.
- Use the proved finite two-connected graph face-cycle theorem to produce a
  polygonal Jordan boundary and bound its whole closed interior by the prescribed
  neighborhood.
- Add native PL sphere and PL disk corollaries in `PolygonalJordan.lean` and
  `PlanarArcNeighborhood.lean`, including finite pairwise disjoint families.
- Follow the project's native no-comment source style. This document retains the
  source attribution and records the mathematical changes. No upstream vendored
  source was edited.

The four public declarations passed `AuditS124ArcNeighborhood`: only `propext`,
`Classical.choice`, and `Quot.sound`.
