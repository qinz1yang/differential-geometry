import RicciFlower.HCGCompactness.MetricCompactness
import RicciFlower.HCGCompactness.RicciFlowConvergence

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci-Flow Solution Compactness

This file gives the theorem-facing MSM135 Theorem 3.10 shape without pretending
that a zeroth-order spacetime curvature bound already supplies the derivative
estimates and smooth-flow Arzela--Ascoli backend.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- Backend that upgrades a time-zero metric Cheeger--Gromov compactness
conclusion to smooth Cheeger--Gromov--Hamilton convergence of the flows.

This is intentionally an explicit input until the Shi-estimate and spacetime
Arzela--Ascoli layer is formalized.  It is also where the currently deferred
mixed time-spatial metric derivative bounds from MSM135 Lemma 3.11 would be
consumed; `FlowDerivativeInput` alone only packages curvature-derivative input
and time-zero bounded geometry. -/
structure SmoothFlowLimitInput
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop where
  upgrade :
    MetricCompactnessConclusion (I := I) (X.atZero (I := I)) ->
      CompactnessConclusion (I := I) X

/-- MSM135 Theorem 3.10 as a reduction from metric compactness plus explicit
flow-derivative and smooth-flow upgrade inputs. -/
theorem solutionCompactness
    [I.Boundaryless]
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hcomplete0 : SeqMetricComplete (I := I) (X.atZero (I := I)))
    (_hcurv : SpacetimeCurvBound (I := I) X)
    (hinj : FlowBaseInjBound (I := I) X)
    (hderiv : FlowDerivativeInput (I := I) X)
    (hflow : SmoothFlowLimitInput (I := I) X) :
    CompactnessConclusion (I := I) X := by
  let hmetricGeom : SeqBoundedGeometry (I := I) (X.atZero (I := I)) :=
    hderiv.at_zero_geom
  exact hflow.upgrade
    (metricCompactness (I := I) (X.atZero (I := I))
      hcomplete0 hmetricGeom hinj)

end HCGCompactness
end RicciFlower
