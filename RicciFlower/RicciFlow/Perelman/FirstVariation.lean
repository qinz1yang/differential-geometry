import RicciFlower.RicciFlow.Perelman.F
import RicciFlower.Variation.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Canonical first variation interfaces for Perelman's `F`

This file is the book-facing layer for first variations.  The concrete
coordinate calculations used in formula 5.10 remain in
`LeviCivita/Variation.lean` and are consumed below only through future
producers.
-/

noncomputable section

namespace RicciFlower
namespace RicciFlow
namespace Perelman

open MeasureTheory
open RicciFlower.Analysis.Volume
open RicciFlower.Analysis.VolumeVariation
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- A generic first variation of a functional of a metric and a potential along
an admissible path. -/
def HasFirstVariationAt
    (Functional : SmoothRiemannianMetric I M -> (M -> Real) -> Real)
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : Variation.MetricPotentialVariationPath (I := I) g potential)
    (value : Real) : Prop :=
  HasDerivAt (fun s : Real => Functional (path.G.metric s)
    (path.potentialPath s)) value path.base

/-- Scalar curvature and gradient-square data used to evaluate the concrete
measure-theoretic `F` functional along a metric-potential path.

Later realization theorems should identify these functions with the scalar
curvature of `path.G.metric s` and `|grad_{g_s} f_s|^2`. -/
structure FVariationData
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : Variation.MetricPotentialVariationPath (I := I) g potential) where
  scalarCurvaturePath : Real -> M -> Real
  gradPotentialNormSqPath : Real -> M -> Real

/-- Perelman's concrete `F` functional along a canonical metric-potential path. -/
def fFunctionalAlongPath [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : Variation.MetricPotentialVariationPath (I := I) g potential)
    (data : FVariationData (I := I) path) : Real -> Real :=
  fun s : Real =>
    fFunctional
      (volumeMeasureFamily (I := I) (M := M) path.G s)
      (data.scalarCurvaturePath s) (data.gradPotentialNormSqPath s)
      (path.potentialPath s)

/-- `F` has first variation `value` along a canonical metric-potential path. -/
def HasFVariationPath [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : Variation.MetricPotentialVariationPath (I := I) g potential)
    (data : FVariationData (I := I) path) (value : Real) : Prop :=
  HasDerivAt (fFunctionalAlongPath (I := I) (M := M) path data) value
    path.base

/-- Book-facing `δ_(v,h)F(g,f)` predicate: the path is admissible in direction
`(v,h)`, and the concrete `F` functional has first variation `value` along it. -/
def FHasVariation [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : Variation.MetricPotentialVariationPath (I := I) g potential)
    (metricVariation :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (potentialVariation : M -> Real)
    (data : FVariationData (I := I) path) (value : Real) : Prop :=
  Variation.IsMetricPotentialVariationPath (I := I) path metricVariation
      potentialVariation ∧
    HasFVariationPath (I := I) (M := M) path data value

/-- The integral value appearing in formula 5.10. -/
def formula510Value [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (potential scalarCurvature lapPotential
      gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess : M -> Real) : Real :=
  ∫ x,
    fFunctionalFormula510Integrand scalarCurvature lapPotential
      gradPotentialNormSq potentialVariation metricVariationTrace
      metricVariationRicciHess x
    ∂(expNegPotentialWeightedMeasure
      (riemannianVolumeMeasure (I := I) (M := M) g) potential)

/-- High-level regularity and realization hypotheses for formula 5.10.

This contains only book-facing analytic/geometric data, not the coordinate
derivative predicates from `LeviCivita/Variation.lean`.  Those predicates
should be supplied by theorem-level regularity rules, not by a bundled
component package. -/
structure PerelmanFVariationRegularity
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : Variation.MetricPotentialVariationPath (I := I) g potential)
    (data : FVariationData (I := I) path)
    (metricVariation :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (potentialVariation scalarCurvature lapPotential gradPotentialNormSq
      metricVariationTrace metricVariationRicciHess : M -> Real) : Prop where
  scalar_base : data.scalarCurvaturePath path.base = scalarCurvature
  grad_base : data.gradPotentialNormSqPath path.base = gradPotentialNormSq
  metric_trace :
    ∀ x : M,
      traceTimeDerivMetricAt (I := I) path.G path.base x =
        metricVariationTrace x
  formula_integrable :
    Integrable
      (fFunctionalFormula510Integrand scalarCurvature lapPotential
        gradPotentialNormSq potentialVariation metricVariationTrace
        metricVariationRicciHess)
      (expNegPotentialWeightedMeasure
        (riemannianVolumeMeasure (I := I) (M := M) g) potential)

/-- MSM135 formula 5.10 in its canonical first-variation form.

The proof frontier is deliberately the whole reformulated theorem, not a new
family of small wrapper hypotheses.  The existing component assembly theorem
`formula510_producer` should be used to fill this statement after the
path-level variation rules produce the needed metric, Christoffel, scalar, and
integral variation theorems. -/
theorem f_firstVariation_formula510
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : Variation.MetricPotentialVariationPath (I := I) g potential)
    (metricVariation :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (potentialVariation scalarCurvature lapPotential gradPotentialNormSq
      metricVariationTrace metricVariationRicciHess : M -> Real)
    (data : FVariationData (I := I) path)
    (hpath :
      Variation.IsMetricPotentialVariationPath (I := I) path metricVariation
        potentialVariation)
    (_hreg :
      PerelmanFVariationRegularity (I := I) (M := M) path data
        metricVariation potentialVariation scalarCurvature lapPotential
        gradPotentialNormSq metricVariationTrace metricVariationRicciHess) :
    FHasVariation (I := I) (M := M) path metricVariation potentialVariation
      data
      (formula510Value (I := I) (M := M) g potential scalarCurvature
        lapPotential gradPotentialNormSq potentialVariation
        metricVariationTrace metricVariationRicciHess) := by
  refine ⟨hpath, ?_⟩
  -- The remaining proof is the intended high-level bridge:
  -- canonical path -> theorem-level variation rules -> `formula510_producer`.
  sorry

end Perelman
end RicciFlow
end RicciFlower
