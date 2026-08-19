import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TailFrameRegularity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
theorem rm04EvolTail_at
    {alpha t0 omega : Real} {hAlphaOmega : alpha < omega} {hT0Omega : t0 < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    {St : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t0 omega hT0Omega)}
    (hS : IsSolutionOn (I := I) S)
    (hAlphaT0 : alpha < t0)
    (hSt : St = S.timeRestrict (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t0 omega hT0Omega))
    (x₀ : M)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t0 omega hT0Omega))
    (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real ↦ solutionCurvatureComponents (I := I) St x₀ s x₀ m)
      (rmLap (coordInv (I := I) St x₀ (t : Real) x₀)
            (nab2RmComp (I := I) St x₀ (t : Real) x₀) (m 0) (m 1) (m 2) (m 3)
        - 2 * (uhlenbeckBTensorInFrame (coordInv (I := I) St x₀) (rmComp (I := I) St x₀)
                (t : Real) x₀ (m 0) (m 1) (m 2) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) St x₀) (rmComp (I := I) St x₀)
                (t : Real) x₀ (m 0) (m 1) (m 3) (m 2)
            + uhlenbeckBTensorInFrame (coordInv (I := I) St x₀) (rmComp (I := I) St x₀)
                (t : Real) x₀ (m 0) (m 2) (m 1) (m 3)
            - uhlenbeckBTensorInFrame (coordInv (I := I) St x₀) (rmComp (I := I) St x₀)
                (t : Real) x₀ (m 0) (m 3) (m 1) (m 2))
        - riemann04RicciDriftInFrame
            (ricciOneUpCompInFrame (I := I) St (coordInv (I := I) St x₀)
              (coordinateFrameAt (I := I) x₀))
            (rmComp (I := I) St x₀) (t : Real) x₀ (m 0) (m 1) (m 2) (m 3))
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t0 omega hT0Omega).carrier (t : Real) := by
  subst hSt
  exact rm04Evol_at (I := I) _ (isSoln_tailRestrict (I := I) hS hAlphaT0 hT0Omega) x₀
    (coordInvDt (I := I) _ x₀)
    (tailCoordFrameReg (I := I) hS hAlphaT0 hT0Omega x₀) t m

omit [NeZero (Module.finrank ℝ E)] in
theorem rm04EvolFamTail
    {alpha t0 omega : Real} {hAlphaOmega : alpha < omega} {hT0Omega : t0 < omega}
    {S : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    {St : SolutionOn (I := I) (M := M)
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t0 omega hT0Omega)}
    (hS : IsSolutionOn (I := I) S)
    (hAlphaT0 : alpha < t0)
    (hSt : St = S.timeRestrict (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t0 omega hT0Omega)) :
    Riemann04BTensorWithRicciDriftEvolutionInFrameOn
      (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen t0 omega hT0Omega)
      (rm04Fam (I := I) St) (rm04LapFam (I := I) St) (rm04BFam (I := I) St)
      (ricUpFam (I := I) St) := by
  subst hSt
  exact rm04EvolFam (I := I) _ (isSoln_tailRestrict (I := I) hS hAlphaT0 hT0Omega)
    (fun y => coordInvDt (I := I) _ y)
    (fun y => tailCoordFrameReg (I := I) hS hAlphaT0 hT0Omega y)

end DifferentialGeometry.PDE.RicciFlow
