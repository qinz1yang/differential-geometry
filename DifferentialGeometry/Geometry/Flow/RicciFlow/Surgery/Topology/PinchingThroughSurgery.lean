import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem pinchingThroughSurgery (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    PinchingThroughSurgery P₀ g₀ := by
  obtain ⟨phi, hphi, hslab⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀
  intro B _
  refine ⟨phi, 1, 1, 1, hphi, one_pos, one_pos, one_pos, ?_⟩
  intro p₀ δbound ρbound _ _ _ H hH k s G hG
  obtain ⟨initial⟩ := hH.1
  obtain ⟨p, -, -, -, -, -, records, -, -, -⟩ := hH.2.2.2.1
  exact hslab H.toHistory initial p records k s G hG.2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
