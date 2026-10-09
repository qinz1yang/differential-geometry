import DifferentialGeometry.Geometry.Metric.Scaling

/-!
# The same model field under radial normalization

Constant metric normalization preserves the length and pairings of the corresponding scaled
vectors. The field remains the original field multiplied by the original normalization radius.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem normalizedMetric_inner_scaled (g : SmoothRiemannianMetric I M)
    {R : ℝ} (hR : 0 < R) (q : M) (v w : TangentSpace I q) :
    (scaleMetric ((R⁻¹) ^ 2) (sq_pos_of_pos (inv_pos.mpr hR)) g).inner q
      (R • v) (R • w) = g.inner q v w := by
  simp only [scaleMetric_inner, map_smul, smul_apply, smul_eq_mul]
  field_simp

theorem normalizedMetric_length_scaled (g : SmoothRiemannianMetric I M)
    {R : ℝ} (hR : 0 < R) (q : M) (v : TangentSpace I q) :
    Real.sqrt ((scaleMetric ((R⁻¹) ^ 2) (sq_pos_of_pos (inv_pos.mpr hR)) g).inner q
      (R • v) (R • v)) = Real.sqrt (g.inner q v v) := by
  rw [normalizedMetric_inner_scaled g hR]

theorem normalizedMetric_pairing_margin (g : SmoothRiemannianMetric I M)
    {R : ℝ} (hR : 0 < R) (q : M) (v w : TangentSpace I q)
    (hw : g.inner q v w ≤ -(1 / 4)) :
    (scaleMetric ((R⁻¹) ^ 2) (sq_pos_of_pos (inv_pos.mpr hR)) g).inner q
      (R • v) (R • w) ≤ -(1 / 4) := by
  rwa [normalizedMetric_inner_scaled g hR]

theorem normalizedMetric_field_bound (g : SmoothRiemannianMetric I M)
    {R : ℝ} (hR : 0 < R) (q : M) (v : TangentSpace I q) (hv : g.inner q v v ≤ 4) :
    Real.sqrt ((scaleMetric ((R⁻¹) ^ 2) (sq_pos_of_pos (inv_pos.mpr hR)) g).inner q
      (R • v) (R • v)) ≤ 2 := by
  rw [normalizedMetric_inner_scaled g hR]
  exact (Real.sqrt_le_sqrt hv).trans_eq (by norm_num)

theorem normalizedMetric_radius_two_unit_pair (g : SmoothRiemannianMetric I M)
    (q : M) (v : TangentSpace I q) (hv : g.inner q v v = 1) :
    (scaleMetric ((2⁻¹ : ℝ) ^ 2) (by norm_num) g).inner q ((2 : ℝ) • v) ((2 : ℝ) • v) = 1 ∧
      (scaleMetric ((2⁻¹ : ℝ) ^ 2) (by norm_num) g).inner q ((2 : ℝ) • v) ((2 : ℝ) • -v) = -1 := by
  constructor
  · rw [normalizedMetric_inner_scaled g (R := 2) (by norm_num), hv]
  · rw [normalizedMetric_inner_scaled g (R := 2) (by norm_num), map_neg, hv]

end DifferentialGeometry.Geometry.Collapse
