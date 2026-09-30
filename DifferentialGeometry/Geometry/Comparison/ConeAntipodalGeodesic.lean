import DifferentialGeometry.Geometry.Comparison.ConeComparisonAngle
import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_antipodal_segment_through_of_cone_comparison
    {Y : Type*} [MetricSpace Y]
    (hdiam : ∀ a b : Y, dist a b ≤ Real.pi)
    (hcomp : fourPointComparison 0 (univ : Set (EuclideanCone Y)))
    (hstrict : ∀ a b : Y, dist a b < Real.pi →
      ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    {a b c : Y} (hab : dist a b = Real.pi) (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      (∀ s t, dist (f s) (f t) = Real.pi * dist s t) ∧
      f ⟨dist a c / Real.pi, div_nonneg dist_nonneg Real.pi_pos.le,
        (div_le_one Real.pi_pos).mpr (hdiam a c)⟩ = c ∧
      ∃ (α : Icc (0 : ℝ) (dist a c) → Y) (β : Icc (0 : ℝ) (dist c b) → Y),
        Isometry α ∧ Isometry β ∧
        α ⟨0, le_rfl, dist_nonneg⟩ = a ∧
        α ⟨dist a c, dist_nonneg, le_rfl⟩ = c ∧
        β ⟨0, le_rfl, dist_nonneg⟩ = c ∧
        β ⟨dist c b, dist_nonneg, le_rfl⟩ = b ∧
        (∀ s : Icc (0 : ℝ) (dist a c),
          f ⟨(s : ℝ) / Real.pi, div_nonneg s.property.1 Real.pi_pos.le,
            (div_le_one Real.pi_pos).mpr (s.property.2.trans (hdiam a c))⟩ = α s) ∧
        ∀ t : Icc (0 : ℝ) (dist c b),
          f ⟨(dist a c + t) / Real.pi,
            div_nonneg (add_nonneg dist_nonneg t.property.1) Real.pi_pos.le,
            (div_le_one Real.pi_pos).mpr (by
              have hsum := dist_add_eq_pi_of_cone_comparison hdiam hcomp hab c
              linarith [t.property.2])⟩ = β t := by
  have hsum := dist_add_eq_pi_of_cone_comparison hdiam hcomp hab c
  have hA : 0 < dist a c := dist_pos.mpr (Ne.symm hca)
  have hB : 0 < dist c b := dist_pos.mpr hcb
  have hApi : dist a c < Real.pi := by linarith
  have hBpi : dist c b < Real.pi := by linarith
  obtain ⟨g, _, hg0, hg1, hgd⟩ := hstrict a c hApi
  obtain ⟨h, _, hh0, hh1, hhd⟩ := hstrict c b hBpi
  obtain ⟨α, hα, hα0, hα1⟩ := exists_isometric_segment_of_dist_eq_mul hg0 hg1 hgd
  obtain ⟨β, hβ, hβ0, hβ1⟩ := exists_isometric_segment_of_dist_eq_mul hh0 hh1 hhd
  obtain ⟨σ, hσ, hl, hr⟩ := exists_isometric_segment_concat hA.le hB.le hα hβ
    (hα1.trans hβ0.symm) (by rw [hα0, hβ1, hab, hsum])
  let f : Icc (0 : ℝ) 1 → Y := fun t =>
    σ ⟨Real.pi * t, mul_nonneg Real.pi_pos.le t.property.1, by
      rw [hsum]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left t.property.2 Real.pi_pos.le⟩
  have hfd (s t : Icc (0 : ℝ) 1) : dist (f s) (f t) = Real.pi * dist s t := by
    dsimp only [f]
    rw [hσ.dist_eq]
    change |Real.pi * (s : ℝ) - Real.pi * (t : ℝ)| = Real.pi * |(s : ℝ) - t|
    rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos]
  have hf : LipschitzWith ⟨Real.pi, Real.pi_pos.le⟩ f :=
    LipschitzWith.of_dist_le_mul (fun s t => (hfd s t).le)
  have hf0 : f ⟨0, by norm_num⟩ = a := by
    have hh := (hl ⟨0, le_rfl, hA.le⟩).trans hα0
    simpa only [f, mul_zero] using hh
  have hf1 : f ⟨1, by norm_num⟩ = b := by
    have hh := (hr ⟨dist c b, hB.le, le_rfl⟩).trans hβ1
    dsimp only [f]
    apply (congrArg σ ?_).trans hh
    apply Subtype.ext
    dsimp
    linarith only [hsum]
  have hleft (s : Icc (0 : ℝ) (dist a c)) :
      f ⟨(s : ℝ) / Real.pi, div_nonneg s.property.1 Real.pi_pos.le,
        (div_le_one Real.pi_pos).mpr (s.property.2.trans (hdiam a c))⟩ = α s := by
    dsimp only [f]
    apply (congrArg σ ?_).trans (hl s)
    apply Subtype.ext
    dsimp
    field_simp
  have hright (t : Icc (0 : ℝ) (dist c b)) :
      f ⟨(dist a c + t) / Real.pi,
        div_nonneg (add_nonneg dist_nonneg t.property.1) Real.pi_pos.le,
        (div_le_one Real.pi_pos).mpr (by linarith [t.property.2])⟩ = β t := by
    dsimp only [f]
    apply (congrArg σ ?_).trans (hr t)
    apply Subtype.ext
    dsimp
    field_simp
  have hfc : f ⟨dist a c / Real.pi, div_nonneg dist_nonneg Real.pi_pos.le,
      (div_le_one Real.pi_pos).mpr (hdiam a c)⟩ = c :=
    (hleft ⟨dist a c, hA.le, le_rfl⟩).trans hα1
  exact ⟨f, hf.continuous, hf0, hf1, hfd, hfc,
    α, β, hα, hβ, hα0, hα1, hβ0, hβ1, hleft, hright⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
