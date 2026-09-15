import DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Basic
import Mathlib.Topology.MetricSpace.Holder

noncomputable section

open MeasureTheory Set
open scoped Convolution NNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}

private theorem integrable_mollifier_mul {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun y => mollifierEps hε y * f (x - y)) volume := by
  exact ((mollifierEps_continuous hε).mul
    (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((mollifierEps_compactSupport hε).mul_right)

theorem le_mollifyEps_of_le {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) {c : ℝ}
    (hc : ∀ x, c ≤ f x) (x : EuclideanSpace ℝ (Fin d)) :
    c ≤ mollifyEps hε f x := by
  calc
    c = ∫ y : EuclideanSpace ℝ (Fin d), mollifierEps hε y * c := by
      rw [integral_mul_const, mollifierEps_integral_eq_one, one_mul]
    _ ≤ mollifyEps hε f x := by
      rw [mollifyEps_apply]
      exact integral_mono ((mollifierEps_integrable hε).mul_const c)
        (integrable_mollifier_mul hε hf x) (fun y =>
          mul_le_mul_of_nonneg_left (hc _) (mollifierEps_nonneg hε y))

theorem mollifyEps_le_of_le {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) {c : ℝ}
    (hc : ∀ x, f x ≤ c) (x : EuclideanSpace ℝ (Fin d)) :
    mollifyEps hε f x ≤ c := by
  calc
    mollifyEps hε f x ≤ ∫ y : EuclideanSpace ℝ (Fin d), mollifierEps hε y * c := by
      rw [mollifyEps_apply]
      exact integral_mono (integrable_mollifier_mul hε hf x)
        ((mollifierEps_integrable hε).mul_const c) (fun y =>
          mul_le_mul_of_nonneg_left (hc _) (mollifierEps_nonneg hε y))
    _ = c := by rw [integral_mul_const, mollifierEps_integral_eq_one, one_mul]

private theorem norm_mollifyEps_sub_le {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    {x y : EuclideanSpace ℝ (Fin d)} {C : ℝ}
    (hC : ∀ z, ‖f (x - z) - f (y - z)‖ ≤ C) :
    ‖mollifyEps hε f x - mollifyEps hε f y‖ ≤ C := by
  rw [mollifyEps_apply, mollifyEps_apply,
    ← integral_sub (integrable_mollifier_mul hε hf x) (integrable_mollifier_mul hε hf y)]
  calc
    ‖∫ z, mollifierEps hε z * f (x - z) - mollifierEps hε z * f (y - z)‖ ≤
        ∫ z, mollifierEps hε z * C := by
      apply norm_integral_le_of_norm_le ((mollifierEps_integrable hε).mul_const C)
      filter_upwards with z
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (mollifierEps_nonneg hε z)]
      exact mul_le_mul_of_nonneg_left (hC z) (mollifierEps_nonneg hε z)
    _ = C := by rw [integral_mul_const, mollifierEps_integral_eq_one, one_mul]

theorem holderWith_mollifyEps {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K α : ℝ≥0}
    (hα : 0 < α) (hf : HolderWith K α f) :
    HolderWith K α (mollifyEps hε f) := by
  intro x y
  have hnorm : dist (mollifyEps hε f x) (mollifyEps hε f y) ≤
      (K : ℝ) * dist x y ^ (α : ℝ) := by
    rw [dist_eq_norm]
    apply norm_mollifyEps_sub_le hε (hf.continuous hα)
    intro z
    simpa only [← dist_eq_norm, dist_sub_right] using hf.dist_le (x - z) (y - z)
  rw [edist_dist, edist_dist]
  calc
    ENNReal.ofReal (dist (mollifyEps hε f x) (mollifyEps hε f y)) ≤
        ENNReal.ofReal ((K : ℝ) * dist x y ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal hnorm
    _ = _ := by
      rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg]

theorem norm_mollifyEps_sub_le_of_holderWith {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K α : ℝ≥0}
    (hα : 0 < α) (hf : HolderWith K α f) (x : EuclideanSpace ℝ (Fin d)) :
    ‖mollifyEps hε f x - f x‖ ≤ (K : ℝ) * ε ^ (α : ℝ) := by
  have hc : (∫ y : EuclideanSpace ℝ (Fin d), mollifierEps hε y * f x) = f x := by
    rw [integral_mul_const, mollifierEps_integral_eq_one, one_mul]
  rw [mollifyEps_apply, ← hc,
    ← integral_sub (integrable_mollifier_mul hε (hf.continuous hα) x)
      ((mollifierEps_integrable hε).mul_const (f x))]
  calc
    ‖∫ y, mollifierEps hε y * f (x - y) - mollifierEps hε y * f x‖ ≤
      ∫ y : EuclideanSpace ℝ (Fin d), mollifierEps hε y *
        ((K : ℝ) * ε ^ (α : ℝ)) := by
      apply norm_integral_le_of_norm_le
        ((mollifierEps_integrable hε).mul_const ((K : ℝ) * ε ^ (α : ℝ)))
      filter_upwards with y
      by_cases hy : mollifierEps hε y = 0
      · simp only [hy, zero_mul, sub_self, norm_zero, le_refl]
      · have hynorm : ‖y‖ ≤ ε := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using
            mollifierEps_support_subset_closedBall_eps hε hy
        have hdist : dist (x - y) x ≤ ε := by
          simpa [dist_eq_norm] using hynorm
        have hbound : ‖f (x - y) - f x‖ ≤ (K : ℝ) * ε ^ (α : ℝ) := by
          simpa only [← dist_eq_norm] using hf.dist_le_of_le hdist
        rw [← mul_sub, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (mollifierEps_nonneg hε y)]
        exact mul_le_mul_of_nonneg_left hbound (mollifierEps_nonneg hε y)
    _ = _ := by rw [integral_mul_const, mollifierEps_integral_eq_one, one_mul]

end DifferentialGeometry.Analysis.Sobolev
