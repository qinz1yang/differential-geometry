import DifferentialGeometry.Topology.PiecewiseLinear.ArcSubset
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import Mathlib.Topology.Perfect

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

theorem IsPLSphere.preperfect_one {S : Set E} (hS : IsPLSphere 1 S) : Preperfect S := by
  obtain ⟨A, hA, -, hAS⟩ := hS.exists_isPLBall_one_superset_of_ssubset isClosed_empty
    (empty_ssubset.mpr hS.isConnected.nonempty)
  exact hS.isConnected.isPreconnected.preperfect_of_nontrivial (hA.nontrivial.mono hAS)

end DifferentialGeometry.Topology.PiecewiseLinear
