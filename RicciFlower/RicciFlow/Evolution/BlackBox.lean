import RicciFlower.RicciFlow.Evolution.Ricci

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Ricci-Flow Evolution Black Boxes

This file contains explicit assumption packages for analytic time regularity
that is not currently proved in RicciFlower.  These packages assume existence
of the derivatives needed by Section 6.2, but they do not assume coordinate
evolution formulas that are already computed in Lean.  For example,
`dt gInv^{ij} = 2 Ric^{ij}` is still proved from the differentiated inverse
identity; this file only supplies the derivative-existence hypothesis for the
chosen inverse-metric component family.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

/-- Black-box time regularity for inverse-metric components.

This is only the assumption that the supplied inverse components have time
derivatives and that interval derivatives are unique at regular times.  The
coordinate formula `dt gInv^{ij} = 2 Ric^{ij}` is proved by
`inverseMetricEvolutionEquationInFrame_of_inverse_components`, not assumed. -/
structure InverseMetricTimeRegularityBlackBoxInFrameOn
    {D : Realized.RealTimeInterval}
    (gInv : Real -> Realized.InverseMetricComponents M Idx) where
  gInvDt : Real -> M -> Idx -> Idx -> Real
  inverseMetricDerivative :
    InverseMetricDerivativeComponentsOn (D := D) gInv gInvDt
  uniqueTimeDerivatives :
    forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real)

/-- Lemma 6.1 from inverse-component time regularity and the already-proved
coordinate calculation. -/
theorem inverseMetricEvolution_of_timeRegularityBlackBox
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrameOn (I := I) S gInv frame)
    (hsymm : SymmetricInverseMetricComponentsInFrameOn gInv)
    (hbb : InverseMetricTimeRegularityBlackBoxInFrameOn (M := M) (Idx := Idx)
      (D := D) gInv) :
    InverseMetricEvolutionEquationInFrame (I := I) S gInv frame :=
  inverseMetricEvolutionEquationInFrame_of_inverse_components
    (I := I) S hS gInv hbb.gInvDt frame
    hbb.inverseMetricDerivative hinv hsymm hbb.uniqueTimeDerivatives

/-- Black-box regularity package for Lemma 6.2.

This does not assume connection time regularity or the Christoffel variation
formula.  It keeps only the analytic frontier that time differentiation
commutes with the fixed-base spatial covariant derivative of metric components,
plus the Ricci-flow identification `partial_t g = -2 Ric` after applying that
fixed-base covariant derivative. -/
structure ConnectionVariationBlackBoxInFrameOn
    {D : Realized.RealTimeInterval}
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

/-- The connection black box supplies the one remaining analytic input needed
by the finite-difference Koszul proof. -/
theorem variableMetricConnectionDiffDerivative_of_blackBox
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hunique : forall t : Realized.RealTimeInterval.RegularTime D,
      UniqueDiffWithinAt Real D.carrier (t : Real))
    (hbb : ConnectionVariationBlackBoxInFrameOn (I := I) S frame u nablaRic) :
    VariableMetricConnectionDiffDerivativeInFrameOnLocal
      (I := I) S frame u (christoffelVariationLoweredRHSInFrame nablaRic) :=
  variableMetricConnectionDiffDerivative_of_metricCovDeriv
    (I := I) S hS frame hframe hu hbb.metricCovDerivDt nablaRic
    hbb.metricCovDerivDerivative hbb.metricCovDerivRicciFlow hunique

/-- Use the black-box connection regularity package to obtain raised
Christoffel evolution in Lemma 6.2. -/
theorem christoffelEvolution_of_blackBox
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hmetricFrame :
      MetricFrameTimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt frame u)
    (hbb : ConnectionVariationBlackBoxInFrameOn (I := I) S frame u nablaRic) :
    ChristoffelEvolutionEquationInFrameOn
      (I := I) S gInv frame hframe nablaRic :=
  christoffelEvolution_of_metricFrameTimeRegularity
    (I := I) S hS gInv gInvDt frame hframe hu
    hbb.metricCovDerivDt nablaRic hmetricFrame
    hbb.metricCovDerivDerivative hbb.metricCovDerivRicciFlow

/-- Black-box time-regularity/geometric-frontier package for Lemma 6.3.

This assumes the derivative-frontier facts that are not yet proved from the
time-dependent Levi-Civita curvature construction.  The component expansion,
finite-sum bookkeeping, and Hamilton RHS reduction are still carried out by the
proved Lean theorem `ricciEvolution_of_variation_commutators`. -/
structure RicciEvolutionTimeRegularityBlackBoxInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) where
  nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real
  ricciVariation :
    RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric)
  contractedCommutators :
    RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric

/-- Lemma 6.3 from the Ricci time-regularity black box and the proved
component reduction. -/
theorem ricciEvolution_of_timeRegularityBlackBox
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (hbb : RicciEvolutionTimeRegularityBlackBoxInFrameOn
      (I := I) S Rm04 gInv frame) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame
      (roughLapRicInFrame (M := M) gInv hbb.nabla2Ric) :=
  ricciEvolution_of_variation_commutators
    (I := I) S Rm04 gInv frame hbb.nabla2Ric hInv
    hbb.ricciVariation hbb.contractedCommutators

/-- Aggregate black-box package for the Section 6.2 time-regularity frontiers.

It bundles derivative-existence assumptions for inverse metric, connection, and
Ricci evolution while keeping all coordinate formulas and finite-dimensional
component reductions in the proved evolution files. -/
structure Section62TimeRegularityBlackBoxInFrameOn
    {D : Realized.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> Realized.Tensor04Section (I := I) (M := M))
    (gInv : Real -> Realized.InverseMetricComponents M Idx)
    (gInvDt : Real -> M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real) where
  metricFrame :
    MetricFrameTimeRegularityInFrameOnLocal
      (I := I) S gInv gInvDt frame u
  connection :
    ConnectionVariationBlackBoxInFrameOn (I := I) S frame u nablaRic
  ricci :
    RicciEvolutionTimeRegularityBlackBoxInFrameOn
      (I := I) S Rm04 gInv frame

end Components

end RicciFlow
end RicciFlower
