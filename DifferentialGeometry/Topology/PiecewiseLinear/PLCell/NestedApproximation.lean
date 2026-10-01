import DifferentialGeometry.Topology.PiecewiseLinear.SphericalShellCompression
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.SphereNesting
import DifferentialGeometry.Topology.ClosedBallImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsTopologicalCell.isConnected_compl_of_isBicollared
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsTopologicalCell 3 C)
    (hbi : IsBicollared (frontier C)) : IsConnected Cᶜ := by
  obtain ⟨φ⟩ := hC
  exact isConnected_compl_of_homeomorphClosedBall_of_isBicollared
    (by rw [← Module.finrank_eq_rank']; norm_num) φ hbi

theorem exists_isPLBall_between_nested_topological_cells
    (C₁ C₂ : Set (EuclideanSpace ℝ (Fin 3)))
    (hC₁ : IsTopologicalCell 3 C₁) (hC₂ : IsTopologicalCell 3 C₂)
    (hshell : IsSphericalShell (closure (C₂ \ C₁)) (frontier C₁) (frontier C₂))
    (hbi : IsBicollared (frontier C₂)) :
    ∃ C, IsPLBall 3 C ∧ C₁ ⊆ interior C ∧ C ⊆ interior C₂ := by
  obtain ⟨φ₁⟩ := hC₁
  obtain ⟨φ₂⟩ := hC₂
  obtain ⟨B, hB, hBX, hsep⟩ := hshell.exists_isPLSphere_separates
  have hconn₁ : IsConnected C₁ := by
    have : ConnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      isConnected_iff_connectedSpace.mp (Metric.isConnected_closedBall (by norm_num))
    rw [← range_closedBallParam φ₁]
    exact isConnected_range (continuous_closedBallParam φ₁)
  obtain ⟨D, hD, -, h₁D, hD₂⟩ := hB.exists_isPLBall_between_of_separates
    (isCompact_of_homeomorphClosedBall φ₁).isClosed
    (isCompact_of_homeomorphClosedBall φ₂) hconn₁
    (IsTopologicalCell.isConnected_compl_of_isBicollared (C := C₂) ⟨φ₂⟩ hbi).isPreconnected hBX hsep
  exact ⟨D, hD, h₁D, hD₂⟩

end DifferentialGeometry.Topology.PiecewiseLinear
