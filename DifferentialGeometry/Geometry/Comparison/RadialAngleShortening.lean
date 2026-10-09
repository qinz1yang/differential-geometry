import DifferentialGeometry.Geometry.Comparison.ModelAngleShortening
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.ShortenedAngleLimit

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem comparison_angle_lower_bound_of_radial_shortening {X : Type*} [MetricSpace X]
    {p a b ar br : X} {κ L r θ : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hrL : r ≤ L)
    (ha : dist p a = L) (hb : dist p b = L)
    (har : dist p ar = r) (hbr : dist p br = r)
    (hatail : dist a ar = L - r) (hbtail : dist b br = L - r)
    (hθ : 0 < θ)
    (hangle : θ ≤ comparisonAngleNegCurvature κ (dist p a) (dist p b) (dist a b)) :
    2 * Real.arcsin (max 0 (Real.sin (θ / 2) -
      ((Real.sin (θ / 2))⁻¹ - Real.sin (θ / 2)) / (Real.exp (2 * (Real.sqrt κ * r)) - 1))) ≤
      comparisonAngleNegCurvature κ (dist p ar) (dist p br) (dist ar br) := by
  rw [ha, hb] at hangle
  rw [har, hbr]
  have hcL : dist a b ≤ 2 * L := by
    have hh := dist_triangle a p b
    rw [dist_comm a p, ha, hb] at hh
    linarith
  have hdr : dist ar br ≤ 2 * r := by
    have hh := dist_triangle ar p br
    rw [dist_comm ar p, har, hbr] at hh
    linarith
  have htail : dist a b - 2 * (L - r) ≤ dist ar br := by
    have h₁ := dist_triangle a ar b
    have h₂ := dist_triangle ar br b
    rw [hatail] at h₁
    rw [dist_comm br b, hbtail] at h₂
    linarith
  exact Real.two_arcsin_max_le_of_le_sin_half
    (comparisonAngleNegCurvature_mem_Icc κ r r (dist ar br)).1
    (comparisonAngleNegCurvature_mem_Icc κ r r (dist ar br)).2
    (sin_half_comparison_angle_lower_bound_of_shortening hκ hr hrL dist_nonneg hcL
      dist_nonneg hdr htail hθ hangle)

end DifferentialGeometry.Geometry.Comparison.Toponogov
