import DifferentialGeometry.Analysis.Integration.Lp.QuadraticDomination
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher

noncomputable section

open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [SecondCountableTopology F]

theorem tendsto_integral_quadratic_fderiv_of_eventually_lipschitz
    (f : ℕ → ℂ → F) (S : ℕ → Set ℂ) (hS : ∀ n, IsCompact (S n))
    {K : Set F} (hK : IsCompact K) (A : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hA : ContinuousOn A K)
    (hf : ∀ᶠ n in atTop, (∃ C : ℝ≥0, LipschitzWith C (f n)) ∧ MapsTo (f n) (S n) K)
    (hlim : Tendsto (fun n => ∫ z in S n,
      (‖fderiv ℝ (f n) z 1‖ ^ 2 + ‖fderiv ℝ (f n) z Complex.I‖ ^ 2) / 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z in S n,
      (A (f n z) (fderiv ℝ (f n) z 1) (fderiv ℝ (f n) z 1) +
        A (f n z) (fderiv ℝ (f n) z Complex.I) (fderiv ℝ (f n) z Complex.I)) / 2)
      atTop (𝓝 0) := by
  borelize F
  have hnorm : ContinuousOn (fun x => ‖A x‖) K := by
    exact (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnorm
  apply squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hlim.const_mul C)
  filter_upwards [hf] with n hn
  obtain ⟨⟨J, hJ⟩, hmap⟩ := hn
  let μ : Measure ℂ := volume.restrict (S n)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (hS n).measure_ne_top
  have hm (w : ℂ) : MemLp (fun z => fderiv ℝ (f n) z w) 2 μ := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ (f n) w).aestronglyMeasurable
      ((J : ℝ) * ‖w‖)
    exact Eventually.of_forall fun z => ((fderiv ℝ (f n) z).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hJ) (norm_nonneg w))
  have hAc : ContinuousOn (fun z => A (f n z)) (S n) :=
    hA.comp hJ.continuous.continuousOn hmap
  have hAm (v w : F) : AEStronglyMeasurable (fun z => A (f n z) v w) μ :=
    ((hAc.clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      (hS n).measurableSet
  have hAb : ∀ᵐ z ∂μ, ‖A (f n z)‖ ≤ C := by
    filter_upwards [ae_restrict_mem (hS n).measurableSet] with z hz
    exact hC (mem_image_of_mem (fun x => ‖A x‖) (hmap hz))
  exact norm_integral_quadratic_add_div_two_le (fun z => A (f n z)) hAm hAb (hm 1) (hm Complex.I)

end Normed

end DifferentialGeometry.Analysis
