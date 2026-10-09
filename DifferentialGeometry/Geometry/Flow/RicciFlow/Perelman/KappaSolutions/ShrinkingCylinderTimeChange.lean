import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeck
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff _root_.Topology

private local instance cylinderTimeChangeSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩


theorem shrinkingCylinder_scaled_time_error_inner
    (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : s ≤ 0)
    (x : SpatialNeckCylinder) (v w : TangentSpace SpatialNeckCylinderModel x) :
    (scaleMetric a ha (scalarOneShrinkingCylinderMetric (s / a)
      ((div_nonpos_of_nonpos_of_nonneg hs ha.le).trans_lt zero_lt_one))).inner x v w -
      (scalarOneShrinkingCylinderMetric s (hs.trans_lt zero_lt_one)).inner x v w =
        (a - 1) * doubleSphereCylinderMetric.inner x v w := by
  rcases x with ⟨y, z⟩
  rcases v with ⟨v, r⟩
  rcases w with ⟨w, t⟩
  erw [scaleMetric_inner, scalarOneShrinkingCylinderMetric_inner,
    scalarOneShrinkingCylinderMetric_inner, doubleSphereCylinderMetric_inner]
  field_simp [ha.ne']
  ring


theorem shrinkingCylinder_backward_forward_reference_equivalent
    (theta s : ℝ) (htheta : theta ∈ Icc (1 : ℝ) 3) (hs : s ∈ Icc (-1 : ℝ) 0) :
    MetricUniformEquivalentOn (I := SpatialNeckCylinderModel) univ
      (scalarOneShrinkingCylinderMetric (1 - theta) (by linarith [htheta.1]))
      (scalarOneShrinkingCylinderMetric s (hs.2.trans_lt zero_lt_one)) 3 := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨y, z⟩ _ ⟨v, r⟩
  have hround : 0 ≤ (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v v := by
    by_cases hv : v = 0
    · subst v
      exact (map_zero ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y 0)).ge
    · exact ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).pos y v hv).le
  have hlo : 2 * (1 - (1 - theta)) ≤ 3 * (2 * (1 - s)) := by
    linarith [htheta.2, hs.2]
  have hhi : 2 * (1 - s) ≤ 3 * (2 * (1 - (1 - theta))) := by
    linarith [htheta.1, hs.1]
  have hlo' := mul_le_mul_of_nonneg_right hlo hround
  have hhi' := mul_le_mul_of_nonneg_right hhi hround
  erw [scalarOneShrinkingCylinderMetric_inner, scalarOneShrinkingCylinderMetric_inner]
  constructor <;> nlinarith [sq_nonneg r]


theorem shrinkingCylinder_backward_forward_tensor_norm_le
    (theta s : ℝ) (htheta : theta ∈ Icc (1 : ℝ) 3) (hs : s ∈ Icc (-1 : ℝ) 0)
    (x : SpatialNeckCylinder) (r : ℕ) (T : Tensor0SSpace r SpatialNeckCylinderModel x) :
    Real.sqrt (normSq0S (scalarOneShrinkingCylinderMetric s (hs.2.trans_lt zero_lt_one)) x r T) ≤
      Real.sqrt ((3 : ℝ) ^ r) *
        Real.sqrt (normSq0S (scalarOneShrinkingCylinderMetric (1 - theta)
          (by linarith [htheta.1])) x r T) := by
  have heq := shrinkingCylinder_backward_forward_reference_equivalent theta s htheta hs
  exact sqrt_normSq0S_le_of_metric_equiv _ _ x r (by norm_num) (heq.2 x (mem_univ x)) T


theorem strongNeckBackground_scaled_time_error_inner
    (epsilon a : ℝ) (ha : 0 < a) (s : ℝ) (hs : s ≤ 0)
    (x : spatialNeckBuffer epsilon) (v w : TangentSpace SpatialNeckCylinderModel x) :
    (scaleMetric a ha (strongNeckBackgroundMetric epsilon (s / a))).inner x v w -
      (strongNeckBackgroundMetric epsilon s).inner x v w =
        (a - 1) * (strongNeckBackgroundMetric epsilon 0).inner x v w := by
  have hsa : s / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs ha.le
  have hmodel := shrinkingCylinder_scaled_time_error_inner a ha s hs
    (x : SpatialNeckCylinder) v w
  erw [scaleMetric_inner] at hmodel
  rw [scaleMetric_inner, strongNeckBackgroundMetric_of_nonpos epsilon (s / a) hsa,
    strongNeckBackgroundMetric_of_nonpos epsilon s hs,
    strongNeckBackgroundMetric_of_nonpos epsilon 0 le_rfl,
    scalarOneShrinkingCylinderMetric_zero]
  simpa only [SmoothRiemannianMetric.restrictOpen_inner] using hmodel


theorem strongNeckBackground_time_error_hasDerivWithinAt
    (epsilon a : ℝ) (ha : 0 < a) (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0)
    (x : spatialNeckBuffer epsilon) (v w : TangentSpace SpatialNeckCylinderModel x) :
    HasDerivWithinAt (fun t =>
      (scaleMetric a ha (strongNeckBackgroundMetric epsilon (t / a))).inner x v w -
        (strongNeckBackgroundMetric epsilon t).inner x v w) 0 (Icc (-1 : ℝ) 0) s := by
  exact (hasDerivWithinAt_const s (Icc (-1 : ℝ) 0)
    ((a - 1) * (strongNeckBackgroundMetric epsilon 0).inner x v w)).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun t ht =>
      strongNeckBackground_scaled_time_error_inner epsilon a ha t ht.2 x v w)
    (strongNeckBackground_scaled_time_error_inner epsilon a ha s hs.2 x v w)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
