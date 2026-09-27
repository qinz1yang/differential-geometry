import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderOpenCovariantJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderTimeChange
import DifferentialGeometry.Geometry.Metric.Pullback.CovariantDerivative
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff


theorem strongNeckBackground_tensor02CovDeriv_eq
    (epsilon s t : ℝ)
    (A : Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2) (a : ℕ) :
    tensor02CovDeriv A (strongNeckBackgroundMetric epsilon s) a =
      tensor02CovDeriv A (strongNeckBackgroundMetric epsilon t) a := by
  exact shrinkingCylinder_open_tensor02CovDeriv_eq (min s 0) (min t 0)
    ((min_le_right s 0).trans_lt zero_lt_one)
    ((min_le_right t 0).trans_lt zero_lt_one) (spatialNeckBuffer epsilon) A a


theorem strongNeckBackground_backward_forward_covNorm_le
    (epsilon theta s : ℝ) (htheta : theta ∈ Icc (1 : ℝ) 3)
    (hs : s ∈ Icc (-1 : ℝ) 0)
    (A : Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (a : ℕ) (x : spatialNeckBuffer epsilon) :
    tensor02CovDerivNormWith a A
        (strongNeckBackgroundMetric epsilon s) (strongNeckBackgroundMetric epsilon s) x ≤
      Real.sqrt ((3 : ℝ) ^ (a + 2)) * tensor02CovDerivNormWith a A
        (strongNeckBackgroundMetric epsilon (1 - theta))
        (strongNeckBackgroundMetric epsilon (1 - theta)) x := by
  have htheta' : 1 - theta ≤ 0 := sub_nonpos.mpr htheta.1
  have hpoint := (shrinkingCylinder_backward_forward_reference_equivalent
    theta s htheta hs).2 (x : SpatialNeckCylinder) (mem_univ _)
  have hpoint' : ∀ v : TangentSpace SpatialNeckCylinderModel x,
      (3 : ℝ)⁻¹ * (strongNeckBackgroundMetric epsilon (1 - theta)).inner x v v ≤
        (strongNeckBackgroundMetric epsilon s).inner x v v ∧
      (strongNeckBackgroundMetric epsilon s).inner x v v ≤
        3 * (strongNeckBackgroundMetric epsilon (1 - theta)).inner x v v := by
    intro v
    simpa only [strongNeckBackgroundMetric_of_nonpos epsilon s hs.2,
      strongNeckBackgroundMetric_of_nonpos epsilon (1 - theta) htheta',
      SmoothRiemannianMetric.restrictOpen_inner] using hpoint v
  rw [tensor02CovDerivNormWith, tensor02CovDerivNormWith,
    strongNeckBackground_tensor02CovDeriv_eq epsilon s (1 - theta)]
  exact sqrt_normSq0S_le_of_metric_equiv _ _ x (a + 2) (by norm_num) hpoint' _


theorem strongNeckBackground_metric_tensor_parallel
    (epsilon s : ℝ) (a : ℕ) :
    tensor02CovDeriv (metricTensorField (strongNeckBackgroundMetric epsilon 0))
      (strongNeckBackgroundMetric epsilon s) (a + 1) = 0 := by
  rw [strongNeckBackground_tensor02CovDeriv_eq epsilon s 0, tensor02_cov_deriv_eq_cov_deriv_of_field,
    ← metricCovDeriv_eq_covDerivOfField]
  exact covDeriv_self_succ _ a

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
