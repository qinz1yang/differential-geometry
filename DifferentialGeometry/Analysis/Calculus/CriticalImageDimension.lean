import DifferentialGeometry.Analysis.Calculus.CriticalHolder
import Mathlib.Topology.MetricSpace.HausdorffDimension
import DifferentialGeometry.Analysis.Integration.Measure.HausdorffDimension

set_option autoImplicit false
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace DifferentialGeometry.Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [SecondCountableTopology E] {f : E → F} {s : Set E}

theorem dimH_image_le_of_fderiv_eq_zero
    (hf : ∀ x ∈ s, ContDiffAt ℝ 2 f x)
    (hz : ∀ x ∈ s, fderiv ℝ f x = 0) :
    dimH (f '' s) ≤ dimH s / 2 := by
  apply dimH_image_le_of_locally_holder_on (r := 2) (by norm_num)
  intro x hx
  obtain ⟨K, r, hr, hH⟩ := exists_holderOnWith_fderiv_zeroSet_ball (hf x hx)
  refine ⟨K, s ∩ ball x r, inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr)), ?_⟩
  exact hH.mono (fun y hy => ⟨hy.2, hz y hy.1⟩)

theorem addHaar_image_eq_zero_of_fderiv_eq_zero [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [Measure.IsAddHaarMeasure μ]
    (hf : ∀ x ∈ s, ContDiffAt ℝ 2 f x)
    (hz : ∀ x ∈ s, fderiv ℝ f x = 0)
    (hd : dimH s / 2 < Module.finrank ℝ F) : μ (f '' s) = 0 :=
  DifferentialGeometry.MeasureTheory.addHaar_eq_zero_of_dimH_lt μ
    ((dimH_image_le_of_fderiv_eq_zero hf hz).trans_lt hd)

theorem addHaar_image_eq_zero_of_fderiv_eq_zero_of_finrank_lt
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [Measure.IsAddHaarMeasure μ]
    (hf : ∀ x ∈ s, ContDiffAt ℝ 2 f x)
    (hz : ∀ x ∈ s, fderiv ℝ f x = 0)
    (hd : Module.finrank ℝ E < 2 * Module.finrank ℝ F) : μ (f '' s) = 0 := by
  apply addHaar_image_eq_zero_of_fderiv_eq_zero μ hf hz
  have hb : dimH s ≤ (Module.finrank ℝ E : ℝ≥0∞) :=
    (dimH_mono (subset_univ s)).trans_eq (Real.dimH_univ_eq_finrank E)
  apply (ENNReal.div_le_div_right hb 2).trans_lt
  apply (ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
  exact_mod_cast (show Module.finrank ℝ E < Module.finrank ℝ F * 2 by omega)

end DifferentialGeometry.Calculus
