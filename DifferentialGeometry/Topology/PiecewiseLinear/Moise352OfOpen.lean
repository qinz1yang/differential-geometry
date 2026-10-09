/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Endgame
import DifferentialGeometry.Topology.PiecewiseLinear.Moise352InwardPushProof
import DifferentialGeometry.Topology.PiecewiseLinear.OpenSourceReduction

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem moise352_three_of_open : Moise352Open.{u} 3 → Moise352.{u} 3 :=
  moise352_of_inwardPush_of_open moise352InwardPush_three

theorem plApproximationManifold_three_of_open :
    Moise352Open.{u} 3 → PLApproximationManifold.{u} 3 :=
  fun hopen => plApproximationManifold_three_of_moise352 (moise352_three_of_open hopen)

end DifferentialGeometry.Topology.PiecewiseLinear
