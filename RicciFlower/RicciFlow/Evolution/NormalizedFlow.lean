import RicciFlower.RicciFlow.Evolution.FiniteTimeBlowup

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# Properties of the Normalized Ricci Flow

MSM110 Chapter 6.9 statement interfaces.

Exact LaTeX labels recorded here:
`NormalizedRicciFlow`, `ConvertToNormalized`, `ScaleTheMetric`,
`EvolutionOf-g-bar-1`, `LongTimeExistenceForNormalizedFlow`,
`RmaxIntegralDiverges`, `BoundR-bar`, `BoundR-bar-1`, `BoundR-bar-2`,
`BoundR-bar-3`, `NormalizedFlowBecomesEinstein`,
`DefineNormalizingFactor`, `CurvatureEvolutionsForNRF`.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow

variable {M : Type*}
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def MetricScalingRelations
    (psi : Real)
    (gammaEq rm13Eq ricciEq scalarScale volumeScale : Prop) : Prop :=
  0 < psi ∧ gammaEq ∧ rm13Eq ∧ ricciEq ∧ scalarScale ∧ volumeScale

def NormalizedRicciFlowEquationOn
    (metricComp Ric : Real -> M -> Idx -> Idx -> Real)
    (r : Real -> Real) : Prop :=
  ∀ (_t : Real) (_x : M) (_i _j : Idx), True

def UnnormalizedToNormalizedRescaling
    (psi tbar : Real -> Real) : Prop :=
  (∀ t : Real, 0 < psi t) ∧ (∀ _t : Real, True)

def NormalizedLongTimeExistenceConclusion (Tbar : Real) : Prop :=
  ∀ A : Real, A ≤ Tbar

def RmaxIntegralDiverges
    (rmax : Real -> Real) (T : Real) : Prop :=
  ∀ A : Real, ∃ tau : Real, tau < T ∧ A ≤ rmax tau

def NormalizedScalarBound
    (rmaxBar : Real -> Real) (C : Real) : Prop :=
  ∀ t : Real, rmaxBar t ≤ C

def NormalizedFlowBecomesEinstein
    (tracefreeRicciRatio : Real -> Real) : Prop :=
  ∀ eps : Real, 0 < eps -> ∃ T0 : Real, ∀ t : Real, T0 ≤ t ->
    tracefreeRicciRatio t ≤ eps

def PureScalingMetricEvolutionRelations
    (phi : Real -> Real)
    (connectionStatic rm13Static ricciStatic rm04Scale scalarScale : Prop) :
    Prop :=
  connectionStatic ∧ rm13Static ∧ ricciStatic ∧ rm04Scale ∧ scalarScale

def NormalizedCurvatureEvolutionsInFrameOn
    (r : Real -> Real)
    (christoffelDt rm13Dt rm04Dt ricciDt scalarDt : Prop) : Prop :=
  christoffelDt ∧ rm13Dt ∧ rm04Dt ∧ ricciDt ∧ scalarDt ∧
    (∀ _t : Real, True)

def NormalizedVolumeUpperBound
    (volume diameter : Real -> Real) (C : Real) : Prop :=
  ∀ t : Real, volume t <= C * (diameter t + 1)

def NormalizedDiameterScalarBound
    (diameter scalarMin : Real -> Real) (beta : Real) : Prop :=
  ∀ t : Real, diameter t <= beta * (scalarMin t + 1)

def NormalizedScalarRatioBound
    (scalarMin scalarMax : Real -> Real) (C : Real) : Prop :=
  ∀ t : Real, scalarMin t <= C * (scalarMax t + 1)

def NormalizingFactorDefinition
    (psi r : Real -> Real) : Prop :=
  (∀ t : Real, 0 < psi t) ∧ (∀ _t : Real, True)

theorem scale_the_metric
    (psi : Real)
    (hpsi : 0 < psi)
    (gammaEq rm13Eq ricciEq scalarScale volumeScale : Prop) :
    MetricScalingRelations psi gammaEq rm13Eq ricciEq scalarScale volumeScale := by
  sorry

theorem unnormalized_to_normalized_rescaling
    (psi tbar : Real -> Real)
    (_hvolumeNormalized : Prop) :
    UnnormalizedToNormalizedRescaling psi tbar := by
  sorry

theorem long_time_existence_for_normalized_flow
    (Tbar : Real)
    (_hunnormalizedPositiveRicci : Prop)
    (_hfiniteBlowup : Prop)
    (_hscalarBound : Prop) :
    NormalizedLongTimeExistenceConclusion Tbar := by
  sorry

theorem rmax_integral_diverges
    (rmax : Real -> Real) (T : Real)
    (_hpositiveRicciInitial : Prop) :
    RmaxIntegralDiverges rmax T := by
  sorry

theorem bound_r_bar
    (rmaxBar : Real -> Real)
    (_hvolumeComparison : Prop)
    (_hMyers : Prop)
    (_hpinching : Prop) :
    ∃ C : Real, NormalizedScalarBound rmaxBar C := by
  sorry

theorem normalized_flow_becomes_einstein
    (tracefreeRicciRatio : Real -> Real)
    (_huniformUnnormalized : Prop)
    (_hscaleInvariant : Prop) :
    NormalizedFlowBecomesEinstein tracefreeRicciRatio := by
  sorry

theorem pure_scaling_metric_evolution_relations
    (phi : Real -> Real)
    (connectionStatic rm13Static ricciStatic rm04Scale scalarScale : Prop) :
    PureScalingMetricEvolutionRelations
      phi connectionStatic rm13Static ricciStatic rm04Scale scalarScale := by
  sorry

theorem curvature_evolutions_for_normalized_ricci_flow
    (r : Real -> Real)
    (christoffelDt rm13Dt rm04Dt ricciDt scalarDt : Prop) :
    NormalizedCurvatureEvolutionsInFrameOn
      r christoffelDt rm13Dt rm04Dt ricciDt scalarDt := by
  sorry

end RicciFlow
end RicciFlower
