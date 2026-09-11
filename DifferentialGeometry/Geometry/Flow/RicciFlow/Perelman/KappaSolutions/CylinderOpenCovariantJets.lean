import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderCovariantJets
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

private abbrev CylinderModel := EuclideanSpace ℝ (Fin 2) × ℝ


theorem shrinkingCylinder_open_connectionDifference_eq_zero
    (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (U : TopologicalSpace.Opens SpatialNeckCylinder) :
    DifferentialGeometry.PDE.DeTurck.connectionDifference
      ((scalarOneShrinkingCylinderMetric s hs).restrictOpen U)
      ((scalarOneShrinkingCylinderMetric t ht).restrictOpen U) = 0 := by
  classical
  funext x
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨sigma, hsigma⟩ := ContMDiffSection.exists_eq_at
    (I := SpatialNeckCylinderModel) (n := (⊤ : ℕ∞))
    (F := CylinderModel)
    (V := (TangentSpace SpatialNeckCylinderModel : SpatialNeckCylinder → Type _))
    (x : SpatialNeckCylinder) w
  have hdiff := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply
    ((scalarOneShrinkingCylinderMetric s hs).restrictOpen U)
    ((scalarOneShrinkingCylinderMetric t ht).restrictOpen U)
    (mdiffAt_restrictOpen_section U sigma x) v
  have heq :
      metricCov ((scalarOneShrinkingCylinderMetric s hs).restrictOpen U)
        (restrictOpenTangentField U (fun y => sigma y)) x v =
      metricCov ((scalarOneShrinkingCylinderMetric t ht).restrictOpen U)
        (restrictOpenTangentField U (fun y => sigma y)) x v := by
    rw [metricCov_restrictOpen_globalSection, metricCov_restrictOpen_globalSection]
    exact shrinkingCylinder_leviCivita_apply_eq s t hs ht _ _
      sigma.mdifferentiableAt v
  have hzero := hdiff.trans (sub_eq_zero.mpr heq)
  simpa only [restrictOpenTangentField_apply, hsigma, Pi.zero_apply, zero_apply] using hzero


theorem shrinkingCylinder_open_leviCivita_apply_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (U : TopologicalSpace.Opens SpatialNeckCylinder) (x : U)
    (sigma : (y : U) → TangentSpace SpatialNeckCylinderModel y)
    (hsigma : MDifferentiableAt SpatialNeckCylinderModel SpatialNeckCylinderModel.tangent
      (T% sigma) x) (v : TangentSpace SpatialNeckCylinderModel x) :
    leviCivitaConnectionOfMetric ((scalarOneShrinkingCylinderMetric s hs).restrictOpen U)
        sigma x v =
      leviCivitaConnectionOfMetric ((scalarOneShrinkingCylinderMetric t ht).restrictOpen U)
        sigma x v := by
  have hz := congrArg (fun D => D x (sigma x) v)
    (shrinkingCylinder_open_connectionDifference_eq_zero s t hs ht U)
  simp only [Pi.zero_apply, zero_apply] at hz
  have hdiff := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply
    ((scalarOneShrinkingCylinderMetric s hs).restrictOpen U)
    ((scalarOneShrinkingCylinderMetric t ht).restrictOpen U) hsigma v
  exact sub_eq_zero.mp (hdiff.symm.trans hz)


theorem shrinkingCylinder_open_connectionEndomorphism_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (U : TopologicalSpace.Opens SpatialNeckCylinder) (p : U) (y : CylinderModel) :
    DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL
      (leviCivitaConnectionOfMetric ((scalarOneShrinkingCylinderMetric s hs).restrictOpen U)) p y =
    DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL
      (leviCivitaConnectionOfMetric ((scalarOneShrinkingCylinderMetric t ht).restrictOpen U)) p y := by
  classical
  apply ContinuousLinearMap.ext
  intro X
  apply ContinuousLinearMap.ext
  intro v
  by_cases hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target
  · rw [DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL_apply_of_mem _ p hy,
      DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL_apply_of_mem _ p hy]
    have hbase : (extChartAt SpatialNeckCylinderModel p).symm y ∈
        (trivializationAt CylinderModel (TangentSpace SpatialNeckCylinderModel) p).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
        (extChartAt SpatialNeckCylinderModel p).map_target hy
    apply congrArg
    exact shrinkingCylinder_open_leviCivita_apply_eq s t hs ht U _ _
      (DifferentialGeometry.TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
        v hbase) _
  · rw [DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL_apply_of_notMem _ p hy,
      DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL_apply_of_notMem _ p hy]


theorem shrinkingCylinder_open_metricCovDerivStep_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (U : TopologicalSpace.Opens SpatialNeckCylinder) (a : ℕ)
    (A : Tensor0SField (I := SpatialNeckCylinderModel) (M := U) (n := ∞) (a + 2)) :
    metricCovDerivStep ((scalarOneShrinkingCylinderMetric s hs).restrictOpen U) a A =
      metricCovDerivStep ((scalarOneShrinkingCylinderMetric t ht).restrictOpen U) a A := by
  apply ContMDiffSection.ext
  intro x
  rw [metricCovDerivStep_apply, metricCovDerivStep_apply]
  unfold totalNabla0SFun
  rw [shrinkingCylinder_open_connectionEndomorphism_eq s t hs ht U]


theorem shrinkingCylinder_open_tensor02CovDeriv_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (U : TopologicalSpace.Opens SpatialNeckCylinder)
    (A : Tensor0SField (I := SpatialNeckCylinderModel) (M := U) (n := ∞) 2) (a : ℕ) :
    tensor02CovDeriv A ((scalarOneShrinkingCylinderMetric s hs).restrictOpen U) a =
      tensor02CovDeriv A ((scalarOneShrinkingCylinderMetric t ht).restrictOpen U) a := by
  have hstep :
      (fun (b : ℕ) (B : Tensor0SField (I := SpatialNeckCylinderModel)
        (M := U) (n := ∞) (b + 2)) =>
          metricCovDerivStep ((scalarOneShrinkingCylinderMetric s hs).restrictOpen U) b B) =
      (fun (b : ℕ) (B : Tensor0SField (I := SpatialNeckCylinderModel)
        (M := U) (n := ∞) (b + 2)) =>
          metricCovDerivStep ((scalarOneShrinkingCylinderMetric t ht).restrictOpen U) b B) := by
    funext b B
    exact shrinkingCylinder_open_metricCovDerivStep_eq s t hs ht U b B
  unfold tensor02CovDeriv
  rw [hstep]


theorem shrinkingCylinder_open_tensor02CovDerivNormWith_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (U : TopologicalSpace.Opens SpatialNeckCylinder)
    (A : Tensor0SField (I := SpatialNeckCylinderModel) (M := U) (n := ∞) 2) (a : ℕ)
    (gNorm : SmoothRiemannianMetric SpatialNeckCylinderModel U) (x : U) :
    tensor02CovDerivNormWith a A ((scalarOneShrinkingCylinderMetric s hs).restrictOpen U) gNorm x =
      tensor02CovDerivNormWith a A ((scalarOneShrinkingCylinderMetric t ht).restrictOpen U) gNorm x := by
  rw [tensor02CovDerivNormWith, tensor02CovDerivNormWith,
    shrinkingCylinder_open_tensor02CovDeriv_eq s t hs ht U]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
