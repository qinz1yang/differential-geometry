import DifferentialGeometry.Geometry.Measure.Area.CoordinateSpeeds
import DifferentialGeometry.Geometry.Metric.InterpolationSpeed



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]



def geodesicStrip (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ₀ γ₁ : ℝ → M) (z : ℂ) : M :=
  geodesicInterpolation g (γ₀ z.im) (γ₁ z.im) z.re

theorem geodesicStrip_horizontal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : ℝ → M) (z : ℂ) (t : ℝ) :
    geodesicStrip g γ₀ γ₁ (z + (t - z.re) • (1 : ℂ)) =
      geodesicInterpolation g (γ₀ z.im) (γ₁ z.im) t := by
  have hre : (z + (t - z.re) • (1 : ℂ)).re = t := by
    simp only [Complex.add_re, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]
    ring
  have him : (z + (t - z.re) • (1 : ℂ)).im = z.im := by
    simp only [Complex.add_im, Complex.smul_im, Complex.one_im, smul_eq_mul, mul_zero, add_zero]
  simp only [geodesicStrip, hre, him]

theorem geodesicStrip_vertical (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : ℝ → M) (z : ℂ) (t : ℝ) :
    geodesicStrip g γ₀ γ₁ (z + (t - z.im) • Complex.I) =
      geodesicInterpolation g (γ₀ t) (γ₁ t) z.re := by
  have hre : (z + (t - z.im) • Complex.I).re = z.re := by
    simp only [Complex.add_re, Complex.smul_re, Complex.I_re, smul_eq_mul, mul_zero, add_zero]
  have him : (z + (t - z.im) • Complex.I).im = t := by
    simp only [Complex.add_im, Complex.smul_im, Complex.I_im, smul_eq_mul, mul_one]
    ring
  simp only [geodesicStrip, hre, him]



theorem exists_geodesicStrip_density_bound [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ ρ C : ℝ≥0, 0 < ρ ∧ 0 < C ∧ ∀ (γ₀ γ₁ : ℝ → M) (z : ℂ),
      z.re ∈ Icc (0 : ℝ) 1 →
      riemannianEDistOf g (γ₀ z.im) (γ₁ z.im) ≤ (ρ : ℝ≥0∞) →
      MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ₀ z.im →
      MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ₁ z.im →
      riemannianAreaDensity g (geodesicStrip g γ₀ γ₁) z ≤
        C * (riemannianEDistOf g (γ₀ z.im) (γ₁ z.im)).toReal *
          (riemannianCurveSpeed g γ₀ z.im + riemannianCurveSpeed g γ₁ z.im) := by
  obtain ⟨ρ, C, hρ, hC, hspeed⟩ := exists_interpolation_endpoint_speed_bound g
  refine ⟨ρ, C, hρ, hC, fun γ₀ γ₁ z hz hd h₀ h₁ => ?_⟩
  have h := riemannianAreaDensity_le_coordinate_speeds g (geodesicStrip g γ₀ γ₁) z z.re z.im
  have hhor : (fun t => geodesicStrip g γ₀ γ₁ (z + (t - z.re) • (1 : ℂ))) =
      geodesicInterpolation g (γ₀ z.im) (γ₁ z.im) := by
    funext t
    exact geodesicStrip_horizontal g γ₀ γ₁ z t
  have hver : (fun t => geodesicStrip g γ₀ γ₁ (z + (t - z.im) • Complex.I)) =
      fun t => geodesicInterpolation g (γ₀ t) (γ₁ t) z.re := by
    funext t
    exact geodesicStrip_vertical g γ₀ γ₁ z t
  rw [hhor, hver] at h
  have hfin : riemannianEDistOf g (γ₀ z.im) (γ₁ z.im) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hd
  have hs : riemannianCurveSpeed g (geodesicInterpolation g (γ₀ z.im) (γ₁ z.im)) z.re =
      (riemannianEDistOf g (γ₀ z.im) (γ₁ z.im)).toReal :=
    (geodesicInterpolation_spec g).2.2.2.1 _ _ hfin z.re
  rw [hs] at h
  apply h.trans
  calc
    _ ≤ (riemannianEDistOf g (γ₀ z.im) (γ₁ z.im)).toReal *
        (C * (riemannianCurveSpeed g γ₀ z.im + riemannianCurveSpeed g γ₁ z.im)) :=
      mul_le_mul_of_nonneg_left (hspeed z.re hz γ₀ γ₁ z.im hd h₀ h₁) ENNReal.toReal_nonneg
    _ = _ := by ring

end DifferentialGeometry.Geometry
