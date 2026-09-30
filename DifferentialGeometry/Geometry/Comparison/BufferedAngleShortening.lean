import DifferentialGeometry.Geometry.Comparison.BufferedRadialComparison
import DifferentialGeometry.Geometry.Comparison.RadialAngleShortening

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Set Metric

theorem comparison_angle_lower_bound_at_fixed_time_of_long_radial_isometries
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {κ L r T θ : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hbuffer : 256 * r < L)
    {n : ℕ} (hdim : dimH (ball p L) ≤ n)
    (hlocal : ∀ z ∈ ball p L,
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    (γ β : Icc (0 : ℝ) L → X) (hγ : Isometry γ) (hβ : Isometry β)
    (hγ0 : γ ⟨0, ⟨le_rfl, by linarith⟩⟩ = p)
    (hβ0 : β ⟨0, ⟨le_rfl, by linarith⟩⟩ = p)
    (hT : T ∈ Ioc (0 : ℝ) r) (hθ : 0 < θ)
    (hangle : θ ≤ comparisonAngleNegCurvature κ L L
      (dist (γ ⟨L, ⟨by linarith, le_rfl⟩⟩) (β ⟨L, ⟨by linarith, le_rfl⟩⟩))) :
    2 * Real.arcsin (max 0 (Real.sin (θ / 2) -
      ((Real.sin (θ / 2))⁻¹ - Real.sin (θ / 2)) / (Real.exp (2 * (Real.sqrt κ * r)) - 1))) ≤
      comparisonAngleNegCurvature κ T T
        (dist (γ ⟨T, ⟨hT.1.le, by linarith [hT.2]⟩⟩)
          (β ⟨T, ⟨hT.1.le, by linarith [hT.2]⟩⟩)) := by
  have hrL : r ≤ L := by linarith
  have hL : 0 ≤ L := by linarith
  have hγrad (t : Icc (0 : ℝ) L) : dist p (γ t) = t.val := by
    rw [← hγ0, hγ.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub,
      abs_neg, abs_of_nonneg t.property.1]
  have hβrad (t : Icc (0 : ℝ) L) : dist p (β t) = t.val := by
    rw [← hβ0, hβ.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub,
      abs_neg, abs_of_nonneg t.property.1]
  have hγtail : dist (γ ⟨L, ⟨hL, le_rfl⟩⟩) (γ ⟨r, ⟨hr.le, hrL⟩⟩) = L - r := by
    rw [hγ.dist_eq, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hrL)]
  have hβtail : dist (β ⟨L, ⟨hL, le_rfl⟩⟩) (β ⟨r, ⟨hr.le, hrL⟩⟩) = L - r := by
    rw [hβ.dist_eq, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hrL)]
  have hs := comparison_angle_lower_bound_of_radial_shortening hκ hr hrL
    (hγrad ⟨L, ⟨hL, le_rfl⟩⟩) (hβrad ⟨L, ⟨hL, le_rfl⟩⟩)
    (hγrad ⟨r, ⟨hr.le, hrL⟩⟩) (hβrad ⟨r, ⟨hr.le, hrL⟩⟩)
    hγtail hβtail hθ (by simpa only [hγrad, hβrad] using hangle)
  rw [hγrad, hβrad] at hs
  exact hs.trans (comparisonAngleNegCurvature_le_of_radial_isometries_in_local_buffer
    hcurves p hκ.le hr hbuffer hdim hlocal hrL hrL γ β hγ hβ hγ0 hβ0 hT hT)

end DifferentialGeometry.Geometry.Comparison.Toponogov
