import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitUlift
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterface
import DifferentialGeometry.Topology.Manifold.SmallDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs

set_option autoImplicit false

/-! # CH12-CX6: a genuine Type 0 hyperbolic model, then ULift -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

attribute [local instance] uliftChartedSpace isManifold_ulift

theorem exists_small_hyperbolic_model_CX6
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) [ConnectedSpace L.M]
    (O : ManifoldOrientation ThreeModel L.M 3)
    (hc : MetricComplete L) (hcurv : hasConstantSectionalCurvature L.metric (-(1 / 4 : ℝ)))
    (hvol : Integral.Measure.riemannianVolumeMeasure ThreeModel L.M L.metric univ < ⊤) :
    ∃ H : FiniteVolumeHyperbolicModel.{0}, ∃ e : H.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ L.M,
      e H.basepoint = L.basepoint ∧ H.metric = Diffeomorph.pullbackMetricCross L.metric e := by
  obtain ⟨N, tN, cN, sN, ⟨e⟩⟩ := DifferentialGeometry.Manifold.exists_small_diffeomorph
    (I := ThreeModel) (M := L.M) (ContinuousLinearEquiv.refl ℝ ThreeSpace)
  let : TopologicalSpace N := tN
  let : ChartedSpace ThreeSpace N := cN
  let : IsManifold ThreeModel ∞ N := sN
  let : T2Space N := e.toHomeomorph.symm.t2Space
  let : SigmaCompactSpace N := e.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  let : ConnectedSpace N := e.toHomeomorph.connectedSpace_iff.mpr inferInstance
  let O' : Topology.Manifold.SmoothOrientation ThreeModel L.M :=
    Topology.Manifold.smoothOrientationOfManifoldOrientation ThreeModel (by
      simpa only [ThreeSpace, finrank_euclideanSpace_fin] using O)
  let oN := Topology.Manifold.pullbackSmoothOrientation ThreeModel ThreeModel e e.contMDiff
    (fun x => (e.mfderivToContinuousLinearEquiv (by simp) x).bijective) O'
  obtain ⟨ON, _⟩ := Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation ThreeModel oN
  have hgcomplete : RiemannianMetricComplete L.metric := ⟨MetricComplete.complete L hc⟩
  let H : FiniteVolumeHyperbolicModel.{0} :=
    { Carrier := N
      topology := tN
      charts := cN
      smooth := sN
      hausdorff := inferInstance
      sigmaCompact := inferInstance
      connected := inferInstance
      orientation := by simpa only [ThreeSpace, finrank_euclideanSpace_fin] using ON
      metric := Diffeomorph.pullbackMetricCross L.metric e
      basepoint := e.symm L.basepoint
      curvature := by
        intro x v w hvw
        rw [DifferentialGeometry.PDE.RicciFlow.Extinction.Width.sectionalCurvature_pullbackMetricCross]
        refine hcurv _ _ _ ?_
        let A := e.mfderivToContinuousLinearEquiv (by simp) x
        have h := hvw.map' A.toLinearEquiv.toLinearMap (LinearMap.ker_eq_bot.mpr A.injective)
        convert h using 1
        ext i
        fin_cases i <;> rfl
      complete := Geometry.Metric.riemannianMetricComplete_pullbackMetricCross hgcomplete e
      finite_volume := by
        let : MeasurableSpace L.M := borel L.M
        let : BorelSpace L.M := ⟨rfl⟩
        let : MeasurableSpace N := borel N
        let : BorelSpace N := ⟨rfl⟩
        rw [Integral.Measure.riemannianVolumeMeasure_pullback_cross L.metric e,
          Measure.map_apply e.symm.continuous.measurable MeasurableSet.univ]
        exact hvol }
  exact ⟨H, e, e.apply_symm_apply _, rfl⟩

theorem exists_ulift_hyperbolic_model_CX6
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) [ConnectedSpace L.M]
    (O : ManifoldOrientation ThreeModel L.M 3)
    (hc : MetricComplete L) (hcurv : hasConstantSectionalCurvature L.metric (-(1 / 4 : ℝ)))
    (hvol : Integral.Measure.riemannianVolumeMeasure ThreeModel L.M L.metric univ < ⊤) :
    ∃ H : FiniteVolumeHyperbolicModel.{0},
      ∃ e : (uliftModel_S13.{u} H).Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ L.M,
        e (uliftModel_S13.{u} H).basepoint = L.basepoint ∧
        (uliftModel_S13.{u} H).metric = Diffeomorph.pullbackMetricCross L.metric e := by
  obtain ⟨H, e, hp, hg⟩ := exists_small_hyperbolic_model_CX6 L O hc hcurv hvol
  let d : (uliftModel_S13.{u} H).Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ H.Carrier :=
    (uliftDiffeomorph ThreeModel H.Carrier).symm
  refine ⟨H, d.trans e, ?_, ?_⟩
  · exact hp
  · change Diffeomorph.pullbackMetricCross H.metric d = _
    rw [hg, Diffeomorph.pullbackMetricCross_trans]

end GC.LongTime.Ch12
