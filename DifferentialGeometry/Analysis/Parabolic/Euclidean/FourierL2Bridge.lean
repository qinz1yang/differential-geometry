import Mathlib.Analysis.Fourier.LpSpace

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem fourier_toLp_two (f : E → ℂ) (hf₁ : Integrable f)
    (hf₂ : MemLp f 2) (hF₂ : MemLp (𝓕 f) 2) :
    Lp.fourierTransformₗᵢ E ℂ (hf₂.toLp f) = hF₂.toLp (𝓕 f) := by
  have hinj : Function.Injective
      (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2) :=
    LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot
        (E := E) (F := ℂ) (μ := (volume : Measure E)) (p := 2))
  apply hinj
  change
    ((Lp.fourierTransformₗᵢ E ℂ (hf₂.toLp f) :
        Lp ℂ 2 volume) : 𝓢'(E, ℂ)) =
      ((hF₂.toLp (𝓕 f) : Lp ℂ 2 volume) : 𝓢'(E, ℂ))
  calc
    _ = 𝓕 ((hf₂.toLp f : Lp ℂ 2 volume) : 𝓢'(E, ℂ)) := by
      exact (Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f)).symm
    _ = ((hF₂.toLp (𝓕 f) : Lp ℂ 2 volume) : 𝓢'(E, ℂ)) := by
      ext g
      rw [TemperedDistribution.fourier_apply]
      simp only [Lp.toTemperedDistribution_apply]
      calc
        (∫ x, (𝓕 g) x • (hf₂.toLp f) x)
            = ∫ x, (𝓕 (g : E → ℂ)) x • f x := by
              apply integral_congr_ae
              filter_upwards [hf₂.coeFn_toLp] with x hx
              rw [hx, SchwartzMap.fourier_coe]
        _ = ∫ ξ, g ξ • 𝓕 f ξ := by
              change
                (∫ x, VectorFourier.fourierIntegral Real.fourierChar volume
                    (innerₗ E) (g : E → ℂ) x • f x) =
                  ∫ ξ, g ξ • VectorFourier.fourierIntegral Real.fourierChar volume
                    (innerₗ E) f ξ
              simpa only [flip_innerₗ] using
                (VectorFourier.integral_fourierIntegral_smul_eq_flip
                  (V := E) (W := E) (F := ℂ)
                  (μ := (volume : Measure E)) (ν := (volume : Measure E))
                  (e := Real.fourierChar) (L := innerₗ E)
                  Real.continuous_fourierChar
                  continuous_inner g.integrable hf₁)
        _ = ∫ ξ, g ξ • (hF₂.toLp (𝓕 f)) ξ := by
              apply integral_congr_ae
              filter_upwards [hF₂.coeFn_toLp] with ξ hξ
              rw [hξ]

end DifferentialGeometry.Analysis.Parabolic.Euclidean
