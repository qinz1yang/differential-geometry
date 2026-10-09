import DifferentialGeometry.Analysis.Integration.Measure.NormalizedHausdorffMeasure

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped NNReal ENNReal

namespace MeasureTheory

theorem cube_le_normalizedHausdorffMeasure
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {K : ℝ≥0} {f : X → EuclideanSpace ℝ (Fin n)} {s : Set X}
    (hf : LipschitzOnWith K f s) (hK : 0 < K)
    {v : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (himage : {w : EuclideanSpace ℝ (Fin n) | ∀ j, |w j - v j| ≤ r} ⊆ f '' s) :
    ENNReal.ofReal (2 * r) ^ n / (K : ℝ≥0∞) ^ n ≤ normalizedHausdorffMeasure n s := by
  have h := (measure_mono (μ := normalizedHausdorffMeasure n) himage).trans
    (normalizedHausdorffMeasure_image_le hf n)
  rw [normalizedHausdorffMeasure_euclidean, volume_euclidean_coordinate_cube] at h
  apply (ENNReal.div_le_iff_le_mul (Or.inl (pow_ne_zero _ (by exact_mod_cast hK.ne')))
    (Or.inl (ENNReal.pow_ne_top ENNReal.coe_ne_top))).mpr
  simpa only [mul_comm] using h

theorem cube_le_normalizedHausdorffMeasure_three
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {f : X → EuclideanSpace ℝ (Fin 3)} {s : Set X}
    (hf : LipschitzOnWith (NNReal.sqrt 3) f s)
    {v : EuclideanSpace ℝ (Fin 3)} {e : ℝ} (he : 0 < e)
    (himage : {w : EuclideanSpace ℝ (Fin 3) | ∀ j, |w j - v j| ≤ e / 4} ⊆ f '' s) :
    ENNReal.ofReal ((e / 2) ^ 3 / (3 * Real.sqrt 3)) ≤ normalizedHausdorffMeasure 3 s ∧
      0 < (e / 2) ^ 3 / (3 * Real.sqrt 3) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have h := cube_le_normalizedHausdorffMeasure hf (by positivity) himage
  have hK : ((NNReal.sqrt 3 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt 3) := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt]
    norm_num
  have hscale : 2 * (e / 4) = e / 2 := by ring
  rw [hscale, hK, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_pow (by positivity), hs3,
    ← ENNReal.ofReal_div_of_pos (mul_pos (by norm_num) hs)] at h
  exact ⟨h, div_pos (pow_pos (half_pos he) _) (mul_pos (by norm_num) hs)⟩

end MeasureTheory
