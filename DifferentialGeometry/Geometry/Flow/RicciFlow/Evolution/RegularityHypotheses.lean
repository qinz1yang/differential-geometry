import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.ChristoffelAlgebra
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.ChristoffelCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Bianchi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Commutator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateIdentities
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Equation.Lichnerowicz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Estimate.QuadraticForm
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

structure InverseMetricTimeRegularityDataInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx) where
  gInvDt : Real -> M -> Idx -> Idx -> Real
  inverseMetricDerivative :
    InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt
  uniqueTimeDerivatives :
    forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)

omit [SigmaCompactSpace M] in
theorem inverse_metric_evolution_of_time_regularity_data
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InvMetricLocal (I := I) S gInv frame Set.univ)
    (hdata : InverseMetricTimeRegularityDataInFrameOn (M := M) (Idx := Idx)
      (D := D) gInv) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ :=
  inverseMetricEvolutionEquationInFrame_of_inverse_components
    (I := I) (u := Set.univ) S hS gInv hdata.gInvDt frame
    (hdata.inverseMetricDerivative.toLocal Set.univ) hinv hdata.uniqueTimeDerivatives

structure ConnectionVariationDataInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) where
  metricCovDerivDt : Real -> M -> Idx -> Idx -> Idx -> Real
  metricCovDerivDerivative :
    MetricCovDerivDerivativeComponentsInFrameOnLocal
      (I := I) S frame u metricCovDerivDt
  metricCovDerivRicciFlow :
    MetricCovDerivDerivativeIsRicciFlowInFrame metricCovDerivDt nablaRic

omit [Fintype Idx] [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem variable_metric_connection_difference_derivative_of_variation_data
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hdata : ConnectionVariationDataInFrameOn (I := I) S frame u nablaRic) :
    VariableMetricConnectionDiffDerivativeInFrameOnLocal
      (I := I) S frame u (christoffelVariationLoweredRHSInFrame nablaRic) :=
  variableMetricConnectionDiffDerivative_of_metricCovDeriv
    (I := I) S frame hframe hu hdata.metricCovDerivDt nablaRic
    hdata.metricCovDerivDerivative hdata.metricCovDerivRicciFlow

omit [SigmaCompactSpace M] [T2Space M] in
theorem christoffel_evolution_of_connection_variation_data
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hmetricFrame :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (hdata : ConnectionVariationDataInFrameOn (I := I) S frame u nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic :=
  christoffelEvolution_of_metricFrameTimeRegularity
    (I := I) S gInv gInvDt frame hframe hu
    hdata.metricCovDerivDt nablaRic hmetricFrame
    hdata.metricCovDerivDerivative hdata.metricCovDerivRicciFlow

structure RicciEvolutionDataInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) where
  nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real
  ricciVariation :
    RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric)
  contractedCommutators :
    RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricci_evolution_of_variation_data
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hdata : RicciEvolutionDataInFrameOn
      (I := I) S Rm04 gInv frame) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame
      (roughLapRicInFrame (M := M) gInv hdata.nabla2Ric) :=
  ricciEvolution_of_variation_commutators
    (I := I) S Rm04 gInv frame hdata.nabla2Ric
    hdata.ricciVariation hdata.contractedCommutators

end Components

end DifferentialGeometry.PDE.RicciFlow
