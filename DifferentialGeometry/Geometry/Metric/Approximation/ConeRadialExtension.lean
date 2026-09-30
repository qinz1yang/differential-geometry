import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.RadialConeIdentities
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open Set Metric
open scoped NNReal

namespace GC.MetricGeometry

variable {X C : Type*} [MetricSpace X] [MetricSpace C] {p q : X} {o : C} {δ : ℝ}

theorem KleinerLottApprox.exists_outward_point
    (φ : KleinerLottApprox p o δ) (H : RadialConeData o)
    (hsegments : ∀ a b : X, ∃ c : Icc (0 : ℝ) 1 → X,
      Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (c s) (c t) = dist a b * dist s t)
    (hδr : δ < dist p q) (hbuffer : 2 * dist p q + 5 * δ < δ⁻¹) :
    ∃ q', dist p q' = 2 * dist p q ∧
      dist p q ≤ dist q q' ∧ dist q q' < dist p q + 15 * δ := by
  have hδ := φ.error_pos
  let r := dist p q
  let t := dist o (φ.toFun q)
  have hr : 0 < r := hδ.trans hδr
  have hqmem : q ∈ ball p δ⁻¹ := by
    rw [mem_ball, dist_comm]
    linarith
  have ht : |t - r| ≤ δ := by
    simpa only [t, r, dist_comm] using φ.radial_error q hqmem
  have htpos : 0 < t := by linarith [(abs_le.mp ht).1]
  let s : ℝ≥0 := ⟨(2 * r + 4 * δ) / t, (div_pos (by positivity) htpos).le⟩
  let z := H.map s (φ.toFun q)
  have hst : (s : ℝ) * t = 2 * r + 4 * δ := div_mul_cancel₀ _ htpos.ne'
  have hsone : 1 ≤ (s : ℝ) := by
    apply (le_div_iff₀ htpos).mpr
    linarith [(abs_le.mp ht).2]
  have hzrad : dist o z = 2 * r + 4 * δ := by
    rw [H.dist_apex]
    exact hst
  have hqz : dist (φ.toFun q) z = 2 * r + 4 * δ - t := by
    calc
      dist (φ.toFun q) z = dist (H.map 1 (φ.toFun q)) (H.map s (φ.toFun q)) := by
        rw [H.map_one]
      _ = |(1 : ℝ) - s| * t := H.same_ray_dist 1 s (φ.toFun q)
      _ = (s : ℝ) * t - t := by rw [abs_of_nonpos (by linarith)]; ring
      _ = 2 * r + 4 * δ - t := by rw [hst]
  obtain ⟨x, hx, hzx⟩ := φ.coverage_witness z (by rw [dist_comm, hzrad]; linarith)
  have hxrad := abs_le.mp (φ.radial_error x hx)
  rw [dist_comm x p] at hxrad
  have hxmodel := abs_le.mp (abs_dist_sub_le z (φ.toFun x) o)
  rw [dist_comm z o, hzrad] at hxmodel
  have hxlower : 2 * r + δ < dist p x := by linarith
  have hxupper : dist p x < 2 * r + 7 * δ := by linarith
  have hqx : dist q x < r + 8 * δ := by
    have hd := (abs_le.mp (φ.distortion q hqmem x hx)).1
    have hh := dist_triangle (φ.toFun q) z (φ.toFun x)
    rw [hqz] at hh
    linarith [(abs_le.mp ht).1]
  obtain ⟨c, _, hc0, hc1, hcd⟩ := hsegments p x
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isometric_segment_of_dist_eq_mul hc0 hc1 hcd
  have htwo : 2 * r ≤ dist p x := by linarith
  let q' := γ ⟨2 * r, by positivity, htwo⟩
  have hrad : dist p q' = 2 * r := by
    rw [← hγ0, hγ.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub,
      abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * r)]
  have htail : dist x q' = dist p x - 2 * r := by
    conv_lhs => rw [← hγ1, hγ.dist_eq, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr htwo)]
  refine ⟨q', hrad, ?_, ?_⟩
  · have hh := dist_triangle p q q'
    rw [hrad] at hh
    change r ≤ dist q q'
    linarith
  · have hh := dist_triangle q x q'
    rw [htail] at hh
    linarith

theorem KleinerLottApprox.exists_outward_point_on_annulus
    (φ : KleinerLottApprox p o δ) (H : RadialConeData o)
    (hsegments : ∀ a b : X, ∃ c : Icc (0 : ℝ) 1 → X,
      Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (c s) (c t) = dist a b * dist s t)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hδa : δ < a / 10) (hδb : δ < 1 / (4 * b + 20))
    (hq : a ≤ dist p q ∧ dist p q ≤ b) :
    ∃ q', dist p q' = 2 * dist p q ∧
      dist p q ≤ dist q q' ∧ dist q q' < dist p q + 15 * δ := by
  apply φ.exists_outward_point H hsegments (by linarith)
  have hd := (lt_div_iff₀ (by linarith : 0 < 4 * b + 20)).mp hδb
  have hbpos : 0 < b := ha.trans_le hab
  have hδsmall : δ < 1 / 20 := by nlinarith [φ.error_pos]
  rw [inv_eq_one_div]
  apply (lt_div_iff₀ φ.error_pos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hq.2 φ.error_pos.le,
    mul_pos φ.error_pos hbpos]

end GC.MetricGeometry
