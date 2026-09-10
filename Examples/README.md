# Metrics, covering lifts and tangent orientations

The examples exercise the public library on actual geometric objects:

- `FiniteMetrics.lean`: a normalized finite chart-bump metric on the empty
  manifold and on a disjoint union of two three-spheres, plus a coordinate
  bump with the prescribed full-radius support.
- `CoveringLifts.lean`: all four prescribed square edges, compatible adjacent
  edges, fixed lifted endpoints, reversal and concatenation, subrectangles,
  and ordinary and singleton finite real intervals.
- `TangentOrientations.lean`: noncompact Euclidean three-space, a section
  through a prescribed oriented tangent fiber, orientation-changing and
  orientation-preserving linear transitions, two-point fibers, and smooth
  local sheet inverses.

Run these from the repository root after building the library:

```sh
lake build DifferentialGeometry
lake env lean Examples/FiniteMetrics.lean
lake env lean Examples/CoveringLifts.lean
lake env lean Examples/TangentOrientations.lean
```

The finite construction is
`DifferentialGeometry.Geometry.exists_finiteBumpMetric`. It reuses the
library's `localFiber` tensor and retains the explicit normalized formula.
The existing `nonempty_smoothRiemannianMetric` supplies the independent
partition-of-unity existence argument.

The covering API lives under `DifferentialGeometry.Topology.Covering` and
uses Mathlib's actual `IsCoveringMap`, `liftPath` and `liftHomotopy`.
Prescribed-bottom square lifting explicitly swaps the manuscript coordinates
into Mathlib's time/parameter convention and back. The ambient base and total
spaces need no separation or local-connectivity assumptions for these laws.

The orientation cover is built from the actual tangent bundle core, with
fibers canonically equivalent to its algebraic orientation classes.
`DifferentialGeometry.Topology.Manifold.exists_tangent_orientation_of_simply_connected`
returns an orientation of that original bundle with local compatibility;
compactness and a metric are unnecessary. Hausdorffness and countability of
the smooth cover have separate transfer results, and compactness supplies
countability through a finite chart cover.

These APIs implement the reusable mathematics behind the initial metric,
covering-lift and orientation inputs. They do not assert smoothability,
Ricci-flow existence, surgery, or the Poincare conjecture.
