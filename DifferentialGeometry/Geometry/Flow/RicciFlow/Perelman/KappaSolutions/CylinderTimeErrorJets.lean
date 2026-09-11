import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderBackgroundJets
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PullbackTowerBounds


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

private local instance cylinderErrorC1 (epsilon : ℝ) :
    IsManifold SpatialNeckCylinderModel 1 (spatialNeckBuffer epsilon) :=
  IsManifold.of_le (n := ∞) (by decide)


def cylinderTimeErrorJet (epsilon c : ℝ) (q : ℕ) (_s : ℝ) :
    Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2 :=
  if q = 0 then (c - 1) • metricTensorField (strongNeckBackgroundMetric epsilon 0) else 0


theorem cylinderTimeErrorJet_zero (epsilon c : ℝ) (hc : 0 < c)
    (s : ℝ) (hs : s ≤ 0) (x : spatialNeckBuffer epsilon)
    (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    cylinderTimeErrorJet epsilon c 0 s x v =
      (scaleMetric c hc (strongNeckBackgroundMetric epsilon (s / c))).inner x (v 0) (v 1) -
        (strongNeckBackgroundMetric epsilon s).inner x (v 0) (v 1) := by
  rw [strongNeckBackground_scaled_time_error_inner epsilon c hc s hs]
  change (c - 1) * metricTensorField (strongNeckBackgroundMetric epsilon 0) x v = _
  rw [metricTensorField_apply]


theorem cylinderTimeErrorJet_succ (epsilon c s : ℝ) (q : ℕ) :
    cylinderTimeErrorJet epsilon c (q + 1) s = 0 := by
  simp only [cylinderTimeErrorJet, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]


theorem cylinderTimeErrorJet_hasDerivWithinAt (epsilon c : ℝ)
    (q : ℕ) (s : ℝ) (times : Set ℝ) (x : spatialNeckBuffer epsilon)
    (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    HasDerivWithinAt (fun t => cylinderTimeErrorJet epsilon c q t x v)
      (cylinderTimeErrorJet epsilon c (q + 1) s x v) times s := by
  rw [cylinderTimeErrorJet_succ]
  exact hasDerivWithinAt_const s times (cylinderTimeErrorJet epsilon c q s x v)


theorem cylinderTimeErrorJet_spatial_succ (epsilon c s : ℝ) (q a : ℕ) :
    tensor02CovDeriv (cylinderTimeErrorJet epsilon c q s)
      (strongNeckBackgroundMetric epsilon s) (a + 1) = 0 := by
  by_cases hq : q = 0
  · rw [cylinderTimeErrorJet, if_pos hq, tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_smul,
      ← tensor02_cov_deriv_eq_cov_deriv_of_field, strongNeckBackground_metric_tensor_parallel, smul_zero]
  · rw [cylinderTimeErrorJet, if_neg hq, tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_zero_tensor]


theorem cylinderTimeErrorJet_covNorm_le (epsilon c s : ℝ)
    (hs : s ∈ Icc (-1 : ℝ) 0) (q a : ℕ) (x : spatialNeckBuffer epsilon) :
    tensor02CovDerivNormWith a (cylinderTimeErrorJet epsilon c q s)
        (strongNeckBackgroundMetric epsilon s) (strongNeckBackgroundMetric epsilon s) x ≤
      |c - 1| * (3 * Real.sqrt 3) := by
  cases a with
  | zero =>
    by_cases hq : q = 0
    · have hpoint := (shrinkingCylinder_backward_forward_reference_equivalent
        1 s (by norm_num) hs).2 (x : SpatialNeckCylinder) (mem_univ _)
      have hpair : ∀ v : TangentSpace SpatialNeckCylinderModel x,
          (3 : ℝ)⁻¹ * (strongNeckBackgroundMetric epsilon 0).inner x v v ≤
            (strongNeckBackgroundMetric epsilon s).inner x v v ∧
          (strongNeckBackgroundMetric epsilon s).inner x v v ≤
            3 * (strongNeckBackgroundMetric epsilon 0).inner x v v := by
        intro v
        simpa only [sub_self, strongNeckBackgroundMetric_of_nonpos epsilon 0 le_rfl,
          strongNeckBackgroundMetric_of_nonpos epsilon s hs.2,
          SmoothRiemannianMetric.restrictOpen_inner] using hpoint v
      have hn := covNorm0_le (strongNeckBackgroundMetric epsilon 0)
        (strongNeckBackgroundMetric epsilon s) x (C := 3) (by norm_num) hpair
      have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
      rw [hdim] at hn
      change Real.sqrt (normSq0S (strongNeckBackgroundMetric epsilon s) x 2
        (metricTensorField (strongNeckBackgroundMetric epsilon 0) x)) ≤ 3 * Real.sqrt 3 at hn
      rw [cylinderTimeErrorJet, if_pos hq]
      change Real.sqrt (normSq0S (strongNeckBackgroundMetric epsilon s) x 2
        ((c - 1) • metricTensorField (strongNeckBackgroundMetric epsilon 0) x)) ≤ _
      rw [sqrt_normSq0S_smul]
      exact mul_le_mul_of_nonneg_left hn (abs_nonneg _)
    · rw [cylinderTimeErrorJet, if_neg hq, tensor02CovDerivNormWith,
        tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_zero_tensor]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
        MetricFiberData.inner, map_zero, Real.sqrt_zero]
      positivity
  | succ a =>
    rw [tensor02CovDerivNormWith, cylinderTimeErrorJet_spatial_succ]
    simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
      MetricFiberData.inner, map_zero, Real.sqrt_zero]
    positivity

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
