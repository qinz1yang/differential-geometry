import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsTopologicalSolidTorus.isConnected_frontier
    {T : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsTopologicalSolidTorus T)
    (hclosed : IsClosed T) : IsConnected (frontier T) := by
  obtain ⟨φ⟩ := hT.nonempty_homeomorph_frontier hclosed
  let _ : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  exact isConnected_iff_connectedSpace.mpr (φ.connectedSpace_iff.mpr inferInstance)

theorem IsTopologicalSolidTorus.interior_nonempty
    {T : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsTopologicalSolidTorus T) :
    (interior T).Nonempty := by
  obtain ⟨φ⟩ := hT
  obtain ⟨z, hz⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let v : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := ⟨0, by simp⟩
  exact ⟨φ.symm (v, ⟨z, hz⟩),
    mem_interior_of_homeomorph_closedBall_prod_sphere φ v ⟨z, hz⟩ (by simp [v])⟩

end DifferentialGeometry.Topology.PiecewiseLinear
