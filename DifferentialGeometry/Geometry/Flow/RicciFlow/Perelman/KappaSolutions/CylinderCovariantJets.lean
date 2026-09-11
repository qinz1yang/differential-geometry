import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderConnection
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff


theorem shrinkingCylinder_metricCovDerivStep_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1) (a : ℕ)
    (A : Tensor0SField (I := SpatialNeckCylinderModel)
      (M := SpatialNeckCylinder) (n := ∞) (a + 2)) :
    metricCovDerivStep (scalarOneShrinkingCylinderMetric s hs) a A =
      metricCovDerivStep (scalarOneShrinkingCylinderMetric t ht) a A := by
  apply ContMDiffSection.ext
  intro x
  rw [metricCovDerivStep_apply, metricCovDerivStep_apply]
  unfold totalNabla0SFun
  rw [shrinkingCylinder_connectionEndomorphism_eq s t hs ht]


theorem shrinkingCylinder_tensor02CovDeriv_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (A : Tensor0SField (I := SpatialNeckCylinderModel)
      (M := SpatialNeckCylinder) (n := ∞) 2) (a : ℕ) :
    tensor02CovDeriv A (scalarOneShrinkingCylinderMetric s hs) a =
      tensor02CovDeriv A (scalarOneShrinkingCylinderMetric t ht) a := by
  have hstep :
      (fun (b : ℕ) (B : Tensor0SField (I := SpatialNeckCylinderModel)
        (M := SpatialNeckCylinder) (n := ∞) (b + 2)) =>
          metricCovDerivStep (scalarOneShrinkingCylinderMetric s hs) b B) =
      (fun (b : ℕ) (B : Tensor0SField (I := SpatialNeckCylinderModel)
        (M := SpatialNeckCylinder) (n := ∞) (b + 2)) =>
          metricCovDerivStep (scalarOneShrinkingCylinderMetric t ht) b B) := by
    funext b B
    exact shrinkingCylinder_metricCovDerivStep_eq s t hs ht b B
  unfold tensor02CovDeriv
  rw [hstep]


theorem shrinkingCylinder_tensor02CovDerivNormWith_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (A : Tensor0SField (I := SpatialNeckCylinderModel)
      (M := SpatialNeckCylinder) (n := ∞) 2) (a : ℕ)
    (gNorm : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder)
    (x : SpatialNeckCylinder) :
    tensor02CovDerivNormWith a A (scalarOneShrinkingCylinderMetric s hs) gNorm x =
      tensor02CovDerivNormWith a A (scalarOneShrinkingCylinderMetric t ht) gNorm x := by
  rw [tensor02CovDerivNormWith, tensor02CovDerivNormWith,
    shrinkingCylinder_tensor02CovDeriv_eq s t hs ht]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
