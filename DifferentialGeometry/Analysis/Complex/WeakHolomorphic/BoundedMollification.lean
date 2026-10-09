import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology Convolution

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- Normalized positive bump convolutions of the same globally bounded locally integrable
function converge in every nonnegative integrable weighted `L¹` norm. -/
theorem weighted_normed_bump_convolution_sub_tendsto_zero
    (G : ℂ → V) (hG : LocallyIntegrable G volume)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ z, ‖G z‖ ≤ B)
    (ρ : ℕ → ContDiffBump (0 : ℂ))
    (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0))
    {K : ℝ} (hratio : ∀ n, (ρ n).rOut ≤ K * (ρ n).rIn)
    (ψ : ℂ → ℝ) (hψ : Integrable ψ volume) (hψnonneg : ∀ z, 0 ≤ ψ z) :
    (∀ n, Integrable (fun z => ψ z *
      ‖((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) z - G z‖) volume) ∧
    Tendsto (fun n => ∫ z, ψ z *
      ‖((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) z - G z‖)
      atTop (𝓝 0) := by
  let Q (n : ℕ) : ℂ → V :=
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G
  let E (n : ℕ) (z : ℂ) : ℝ := ψ z * ‖Q n z - G z‖
  have hGm : AEStronglyMeasurable G volume := hG.aestronglyMeasurable
  have hQ (n : ℕ) : Continuous (Q n) :=
    (ρ n).hasCompactSupport_normed.continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n).continuous_normed hG
  have hQbound (n : ℕ) (z : ℂ) : ‖Q n z‖ ≤ B := by
    simpa only [dist_zero_right] using
      (dist_convolution_le (x₀ := z) (z₀ := (0 : V)) hB
        (ρ n).support_normed_eq.subset (ρ n).nonneg_normed
        (ρ n).integral_normed hGm (fun y _ => by
          simpa only [dist_zero_right] using hbound y))
  have hEm (n : ℕ) : AEStronglyMeasurable (E n) volume :=
    hψ.aestronglyMeasurable.mul ((hQ n).aestronglyMeasurable.sub hGm).norm
  have hmajor : Integrable (fun z : ℂ => (2 * B) * ψ z) volume :=
    hψ.const_mul (2 * B)
  have hEbound (n : ℕ) : ∀ᵐ z ∂volume, ‖E n z‖ ≤ (2 * B) * ψ z := by
    apply Eventually.of_forall
    intro z
    rw [show E n z = ψ z * ‖Q n z - G z‖ from rfl,
      Real.norm_of_nonneg (mul_nonneg (hψnonneg z) (norm_nonneg _))]
    calc
      _ ≤ ψ z * (B + B) := mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (add_le_add (hQbound n z) (hbound z))) (hψnonneg z)
      _ = _ := by ring
  have hElim : ∀ᵐ z ∂volume, Tendsto (fun n => E n z) atTop (𝓝 0) := by
    filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      hρ (Eventually.of_forall hratio) hG] with z hz
    have hz' : Tendsto (fun n => ‖Q n z - G z‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using
        (hz.sub (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => G z) atTop (𝓝 (G z)))).norm
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ψ z) atTop (𝓝 (ψ z))).mul hz'
  refine ⟨fun n => hmajor.mono' (hEm n) (hEbound n), ?_⟩
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence (fun z : ℂ => (2 * B) * ψ z)
      hEm hmajor hEbound hElim)

end DifferentialGeometry.Analysis
