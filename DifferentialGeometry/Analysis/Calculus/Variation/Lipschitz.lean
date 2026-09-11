import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun








noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis

variable {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} {C : ℝ≥0}


theorem eVariationOn_Icc_le_of_lipschitz (hf : LipschitzWith C f) (a b : ℝ) :
    eVariationOn f (Icc a b) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  simpa only [Function.comp_id, eVariationOn_id_Icc] using
    hf.lipschitzOnWith.comp_eVariationOn_le (g := id) (s := Icc a b) (mapsTo_univ _ _)

theorem eVariationOn_Icc_ne_top_of_lipschitz (hf : LipschitzWith C f) (a b : ℝ) :
    eVariationOn f (Icc a b) ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitz hf a b)


theorem lipschitz_variationOnFromTo (hf : LipschitzWith C f) (a : ℝ) :
    LipschitzWith C (variationOnFromTo f univ a) := by
  have hloc : LocallyBoundedVariationOn f univ := hf.locallyBoundedVariationOn univ
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, variationOnFromTo.sub_right hloc (mem_univ _) (mem_univ _) (mem_univ _)]
  wlog hxy : y ≤ x generalizing x y
  · rw [variationOnFromTo.eq_neg_swap, abs_neg, dist_comm]
    exact this y x (le_of_not_ge hxy)
  rw [variationOnFromTo.eq_of_le f univ hxy, univ_inter, ENNReal.abs_toReal]
  have h := ENNReal.toReal_mono (by finiteness)
    (eVariationOn_Icc_le_of_lipschitz hf y x)
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hxy), Real.dist_eq,
    abs_of_nonneg (sub_nonneg.mpr hxy)] using h


theorem dist_le_variationOnFromTo_dist (hf : LipschitzWith C f) (a x y : ℝ) :
    dist (f x) (f y) ≤ dist (variationOnFromTo f univ a x) (variationOnFromTo f univ a y) := by
  have hloc : LocallyBoundedVariationOn f univ := hf.locallyBoundedVariationOn univ
  rw [Real.dist_eq, variationOnFromTo.sub_right hloc (mem_univ _) (mem_univ _) (mem_univ _)]
  wlog hxy : y ≤ x generalizing x y
  · rw [variationOnFromTo.eq_neg_swap, abs_neg, dist_comm]
    exact this y x (le_of_not_ge hxy)
  rw [variationOnFromTo.eq_of_le f univ hxy, univ_inter, ENNReal.abs_toReal]
  exact BoundedVariationOn.dist_le (eVariationOn_Icc_ne_top_of_lipschitz hf y x)
    ⟨hxy, le_rfl⟩ ⟨le_rfl, hxy⟩



theorem deriv_variationOnFromTo_nonneg (hf : LipschitzWith C f) (a x : ℝ) :
    0 ≤ deriv (variationOnFromTo f univ a) x := by
  have hm : Monotone (variationOnFromTo f univ a) :=
    fun _ _ h => variationOnFromTo.monotoneOn (hf.locallyBoundedVariationOn univ)
      (mem_univ a) (mem_univ _) (mem_univ _) h
  exact hm.deriv_nonneg

end DifferentialGeometry.Analysis
