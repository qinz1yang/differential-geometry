import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.TerminalRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

section Ancient

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem terminalJetContinuous_of_ancientFlow
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) :
    TerminalJetContinuous (I := I3) F 0 := by
  intro k x v
  exact solution_nablaKRm04_eval_continuousWithinAt_terminal F.S F.isSolution
    (a := (-1 : ℝ)) (b := 0) (by norm_num) (fun _ ht => ht.2)
    (fun _ ht => ht.2) k x v

theorem isAncientKappaSolutionTerminal_of_ancient {kappa : ℝ} {D : RealTimeInterval}
    {F : PointedFlowData.{u, 0, 0} I3 D}
    (hF : IsAncientKappaSolution (I := I3) kappa F) :
    IsAncientKappaSolutionTerminal (I := I3) kappa F := by
  refine ⟨hF, ?_⟩
  intro k x v
  apply solution_nablaKRm04_eval_continuousWithinAt_terminal F.S F.isSolution
    (a := (-1 : ℝ)) (b := 0) (by norm_num) _ _ k x v
  · intro t ht
    rw [hF.carrier_eq]
    exact ht.2
  · intro t ht
    rw [hF.regular_eq]
    exact ht.2

end Ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
