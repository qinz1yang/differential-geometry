import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import DifferentialGeometry.Topology.Simplex.NormedBall
import DifferentialGeometry.Topology.Simplex.BoundaryCoordinates

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem IsPLSphere.twoSimplyConnectedSpace [FiniteDimensional ℝ E]
    {B : Set E} (hB : IsPLSphere 2 B) : SimplyConnectedSpace B := by
  obtain ⟨f, hf⟩ := hB
  let e : stdSimplexBoundary 3 ≃ₜ SphereTwo :=
    (stdSimplexBoundaryHomeomorphSimplexBoundary 3).trans
      (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm)
  let _ : SimplyConnectedSpace (stdSimplexBoundary 3) :=
    e.toHomotopyEquiv.simplyConnectedSpace
  exact hf.homeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

end DifferentialGeometry.Topology.PiecewiseLinear
