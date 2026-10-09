import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Geometry.Metric.CompletenessPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiffeomorphismTransport

/-!
# CH12-S13 / IF2 (3): `FiniteVolumeHyperbolicModel.{0} → FiniteVolumeHyperbolicModel.{u}`

`ULift` transport of carrier, manifold structure, metric (pullback along the inverse of the
standard `ULift` diffeomorphism), orientation, completeness, constant curvature and volume.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic Set Manifold
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

open DifferentialGeometry.Topology in
attribute [local instance] uliftChartedSpace isManifold_ulift

def uliftModel_S13 (M : FiniteVolumeHyperbolicModel.{0}) :
    FiniteVolumeHyperbolicModel.{u} :=
  let Φ : ULift.{u} M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier :=
    (uliftDiffeomorph (𝓡 3) M.Carrier).symm
  { Carrier := ULift.{u} M.Carrier
    topology := inferInstance
    charts := uliftChartedSpace _ _
    smooth := isManifold_ulift _ _
    hausdorff := inferInstance
    sigmaCompact := inferInstance
    connected := (Homeomorph.ulift : ULift.{u} M.Carrier ≃ₜ M.Carrier).connectedSpace_iff.mpr
      inferInstance
    orientation := uliftOrientation _ _ M.orientation
    metric := Diffeomorph.pullbackMetricCross M.metric Φ
    basepoint := ULift.up M.basepoint
    curvature := by
      intro x v w hvw
      rw [DifferentialGeometry.PDE.RicciFlow.Extinction.Width.sectionalCurvature_pullbackMetricCross]
      refine M.curvature _ _ _ ?_
      let f := Φ.mfderivToContinuousLinearEquiv (by simp) x
      have h := hvw.map' (f.toLinearEquiv.toLinearMap)
        (LinearMap.ker_eq_bot.mpr f.injective)
      convert h using 1
      ext i
      fin_cases i <;> rfl
    complete := DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
      M.complete Φ
    finite_volume := by
      let : MeasurableSpace M.Carrier := borel _
      have : BorelSpace M.Carrier := ⟨rfl⟩
      let : MeasurableSpace (ULift.{u} M.Carrier) := borel _
      have : BorelSpace (ULift.{u} M.Carrier) := ⟨rfl⟩
      rw [Integral.Measure.riemannianVolumeMeasure_pullback_cross M.metric Φ,
        MeasureTheory.Measure.map_apply Φ.symm.continuous.measurable MeasurableSet.univ]
      exact M.finite_volume }

end GC.LongTime.Ch12
