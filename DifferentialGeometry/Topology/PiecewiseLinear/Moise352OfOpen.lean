/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Endgame
import DifferentialGeometry.Topology.PiecewiseLinear.Moise352InwardPushProof
import DifferentialGeometry.Topology.PiecewiseLinear.OpenSourceReduction

/-!
# Moise 35.2 in dimension three from its open case alone

`moise352InwardPush_three` proves `Moise352InwardPush 3`, and
`moise352_of_inwardPush_of_open` derives `Moise352 n` from the inward push together with the
open case `Moise352Open n`.  Discharging the push leaves `Moise352Open 3` as the only
hypothesis, and `plApproximationManifold_three_of_moise352` carries that on to the endpoint.

This supersedes `moise352_of_inwardPush_of_skeletonExtension` as the reduction step of the
chain.  That theorem reduces nothing: its third hypothesis `Moise352SkeletonExtension 3` has
literally the conclusion of `Moise352 3`, so the implication is modus ponens.  Here the only
remaining hypothesis is a genuine weakening of the goal.

The open obligation `Moise352Open 3` is a statement about open subsets of piecewise linear
three-manifolds only.  Such a source is boundaryless, so every vertex link of a triangulation
of it is a two-sphere, and the §34 argument runs without the exterior patches that a source
with boundary would force on it.

## Main results

* `moise352_three_of_open`: `Moise352Open 3 → Moise352 3`.
* `plApproximationManifold_three_of_open`: `Moise352Open 3 → PLApproximationManifold 3`.
-/

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

/-- **Moise 35.2 in dimension three from its open case**, the inward push being discharged by
`moise352InwardPush_three`. -/
theorem moise352_three_of_open : Moise352Open.{u} 3 → Moise352.{u} 3 :=
  moise352_of_inwardPush_of_open moise352InwardPush_three

/-- **The piecewise linear approximation theorem for three-manifolds from the open case of
Moise 35.2**, by `plApproximationManifold_three_of_moise352`. -/
theorem plApproximationManifold_three_of_open :
    Moise352Open.{u} 3 → PLApproximationManifold.{u} 3 :=
  fun hopen => plApproximationManifold_three_of_moise352 (moise352_three_of_open hopen)

end DifferentialGeometry.Topology.PiecewiseLinear
