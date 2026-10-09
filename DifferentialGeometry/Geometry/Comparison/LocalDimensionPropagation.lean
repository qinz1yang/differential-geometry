import DifferentialGeometry.Geometry.Comparison.EightRadialContraction
import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (p : X) {R : ℝ} (hR : 0 < R)
variable [LocallyCompactSpace (ball p (8 * R))]
variable (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
  @IsOpen (ball p (8 * R))
    (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball p (8 * R))
    (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)

include hcurves hR hlocal

theorem dimH_closedBall_le_dimH_ball_of_intrinsic_8_buffer
    {q : X} (hq : q ∈ ball p (R / 2)) {r : ℝ} (hr : 0 < r) :
    dimH (closedBall p R) ≤ dimH (ball q r) := by
  let δ : ℝ := min R r / 2
  have hδpos : 0 < δ := half_pos (lt_min hR hr)
  have hδR : δ < R := (div_le_div_of_nonneg_right (min_le_left R r) (by norm_num)).trans_lt
    (half_lt_self hR)
  have hδr : δ ≤ r := (div_le_div_of_nonneg_right (min_le_right R r) (by norm_num)).trans
    (half_le_self hr.le)
  obtain ⟨f, hfball, hfd⟩ := exists_radial_contraction_of_intrinsic_8_buffer
    hcurves p hR hlocal hq ⟨hδpos, hδR⟩
  have hsinh : 0 < sinh (2 * R) := sinh_pos_iff.mpr (by positivity)
  have hanti : AntilipschitzWith (NNReal.mk (sinh (2 * R) / δ) (by positivity)) f := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    change dist x.val y.val ≤ (sinh (2 * R) / δ) * dist (f x) (f y)
    have h := mul_le_mul_of_nonneg_left (hfd x y)
      (div_nonneg hsinh.le hδpos.le)
    have he : (sinh (2 * R) / δ) * ((δ / sinh (2 * R)) * dist x.val y.val) =
        dist x.val y.val := by field_simp
    rwa [he] at h
  have himage : f '' (univ : Set (closedBall p R)) ⊆ ball q r := by
    rintro _ ⟨x, _, rfl⟩
    exact (hfball x).trans_le hδr
  have h := (hanti.le_dimH_image (univ : Set (closedBall p R))).trans (dimH_mono himage)
  rw [← isometry_subtype_coe.dimH_image (univ : Set (closedBall p R))] at h
  simpa only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using h

end DifferentialGeometry.Geometry.Comparison.Toponogov
