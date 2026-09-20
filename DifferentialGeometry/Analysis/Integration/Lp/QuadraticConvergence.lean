import DifferentialGeometry.Analysis.Integration.Lp.QuadraticLowerSemicontinuity


noncomputable section

namespace MeasureTheory

open Filter Set
open scoped ENNReal Topology

variable {P X : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem tendsto_integral_quadratic_of_tendsto
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n x y, AEStronglyMeasurable (fun t => B n t x y) μ)
    (hB₀ : ∀ x y, AEStronglyMeasurable (fun t => B₀ t x y) μ)
    (C : ℕ → ℝ) (C₀ : ℝ)
    (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C n)
    (hC₀ : ∀ᵐ t ∂μ, ‖B₀ t‖ ≤ C₀)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ᵐ t ∂μ, ‖B n t - B₀ t‖ ≤ δ)
    (u : ℕ → Lp X 2 μ) (u₀ : Lp X 2 μ)
    (hu : Tendsto u atTop (𝓝 u₀)) :
    Tendsto (fun n => ∫ t, B n t (u n t) (u n t) ∂μ) atTop
      (𝓝 (∫ t, B₀ t (u₀ t) (u₀ t) ∂μ)) := by
  have hweak : ∀ F : Lp X 2 μ →L[ℝ] ℝ,
      Tendsto (fun n => F (u n)) atTop (𝓝 (F u₀)) := fun F =>
    (F.continuous.tendsto u₀).comp hu
  have hcross := tendsto_integral_bilinear_of_weak
    B B₀ hB hB₀ C C₀ hC hC₀ hconv u u₀ u₀ hweak
  let K := max 0 C₀ + 1
  have hK : 0 ≤ K := by positivity
  have hBbound : ∀ᶠ n in atTop, ∀ᵐ t ∂μ, ‖B n t‖ ≤ K := by
    filter_upwards [hconv 1 zero_lt_one] with n hn
    filter_upwards [hn, hC₀] with t ht ht₀
    calc
      ‖B n t‖ = ‖B n t - B₀ t + B₀ t‖ := by
        simpa only using! (congrArg norm (sub_add_cancel (B n t) (B₀ t))).symm
      _ ≤ ‖B n t - B₀ t‖ + ‖B₀ t‖ := by
        simpa only using! norm_add_le (B n t - B₀ t) (B₀ t)
      _ ≤ 1 + C₀ := add_le_add ht ht₀
      _ ≤ K := by dsimp only [K]; linarith only [le_max_right 0 C₀]
  have herrBound : ∀ᶠ n in atTop,
      ‖∫ t, B n t ((u n - u₀) t) (u n t) ∂μ‖ ≤
        K * (‖u n - u₀‖ * ‖u n‖) := by
    filter_upwards [hBbound] with n hn
    exact norm_integral_bilinear_le_lp_norm (B n) (hB n) hK hn (u n - u₀) (u n)
  have herrLimit : Tendsto (fun n => K * (‖u n - u₀‖ * ‖u n‖)) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_mul, mul_zero] using
      ((hu.sub (tendsto_const_nhds (x := u₀))).norm.mul hu.norm).const_mul K
  have herr : Tendsto (fun n => ∫ t, B n t ((u n - u₀) t) (u n t) ∂μ)
      atTop (𝓝 0) := squeeze_zero_norm' herrBound herrLimit
  have heq (n : ℕ) :
      (∫ t, B n t ((u n - u₀) t) (u n t) ∂μ) +
        (∫ t, B n t (u₀ t) (u n t) ∂μ) =
      ∫ t, B n t (u n t) (u n t) ∂μ := by
    rw [← integral_add
      (integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hB n) (hC n)
        (Lp.memLp (u n - u₀)) (Lp.memLp (u n)))
      (integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hB n) (hC n)
        (Lp.memLp u₀) (Lp.memLp (u n)))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) u₀] with t ht
    simp only [ht, Pi.sub_apply, map_sub, sub_apply, sub_add_cancel]
  simpa only [heq, zero_add] using herr.add hcross

end MeasureTheory
