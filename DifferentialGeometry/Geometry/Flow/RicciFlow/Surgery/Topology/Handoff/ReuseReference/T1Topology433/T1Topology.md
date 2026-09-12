# T1Topology

## Scope

This module isolates the Hurewicz half of the Poincare-plan topology input T1.
It turns trivial second homology and nontrivial third homology into nontrivial
third homotopy for a simply connected space.

It does not supply Poincare duality, orientability of simply connected closed
three-manifolds, or their top-dimensional homology calculation.

## Source

The degree-two and degree-three Hurewicz equivalences come from the generated
`T1Topology433/Upstream/T1Provider.lean` extraction of the Lean 4.33
`Solution.lean` source.

## Verification

The generated provider and this public module pass focused Lean 4.33 checks.
The public endpoint `t1_hurewicz` is complete and warning-free.

Progress accounting:

- `t1_hurewicz`, the isolated Hurewicz reduction: 100%;
- the Hurewicz half of T1 infrastructure in this Lean 4.33 project: 100%;
- the full theorem for a closed simply connected 3-manifold: 0%, because it is
  not stated and the duality/orientability/top-homology producer is absent;
- estimated dedicated T1 infrastructure including that missing half: 55-65%;
- the main RicciFlower P0-P9 infrastructure remains about 10-18%, and its final
  Poincare theorem remains 0%, because this module is not yet ported to 4.29.

The broader `TopologyToolbox` adds useful surrounding topology but does not
change the theorem status of the missing manifold-duality half.
