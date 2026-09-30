import DifferentialGeometry.Geometry.Metric.HalfPlanePacking
import DifferentialGeometry.Geometry.Metric.Approximation.ProductFactorComposition
import DifferentialGeometry.Geometry.Metric.Approximation.IntervalTargetExtension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Set Metric
open GC.MetricGeometry

namespace EdgeRegression

private def exactApprox {X : Type*} [MetricSpace X] (p : X) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) : KleinerLottApprox p p ε where
  error_pos := hε
  error_lt_one := hε1
  toFun := id
  basepoint := rfl
  distortion _ _ _ _ := by simp; exact hε.le
  coverage y hy := by
    have hm : y ∈ id '' ball p ε⁻¹ := ⟨y, by change dist y p < ε⁻¹; linarith, rfl⟩
    exact (infDist_le_dist_of_mem hm).trans (by simpa using hε.le)

private def cross (i : Fin 2 × Bool) : WithLp 2 (ℝ × ℝ) :=
  if i.1 = 0 then WithLp.toLp 2 ((if i.2 then -1 else 1), 0)
  else WithLp.toLp 2 (0, (if i.2 then -1 else 1))

theorem exact_cross_has_negative_height :
    (∀ i, ‖cross i‖ = 1) ∧
    (∀ i : Fin 2, dist (cross (i, false)) (cross (i, true)) = 2) ∧
    (∀ s t : Bool, dist (cross (0, s)) (cross (1, t)) = Real.sqrt 2) ∧
    ¬ (∀ i, 0 ≤ (cross i).snd) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨i, s⟩
    fin_cases i <;> cases s <;>
      norm_num [cross, WithLp.prod_norm_eq_of_L2]
  · intro i
    fin_cases i <;> norm_num [cross, WithLp.prod_dist_eq_of_L2, Real.dist_eq]
  · intro s t
    cases s <;> cases t <;> norm_num [cross, WithLp.prod_dist_eq_of_L2, Real.dist_eq]
  · intro h
    have := h (1, true)
    norm_num [cross] at this

theorem repeated_antipodes_need_cross_distances :
    ∃ q : Fin 2 × Bool → WithLp 2 (ℝ × ℝ),
      (∀ i, 0 ≤ (q i).snd ∧ ‖q i‖ = 1) ∧
      (∀ i : Fin 2, dist (q (i, false)) (q (i, true)) = 2) ∧
      dist (q (0, false)) (q (1, false)) = 0 := by
  refine ⟨fun i => WithLp.toLp 2 ((if i.2 then (-1 : ℝ) else 1), (0 : ℝ)), ?_, ?_, ?_⟩
  · rintro ⟨i, s⟩
    cases s <;> norm_num [WithLp.prod_norm_eq_of_L2]
  · intro i
    norm_num [WithLp.prod_dist_eq_of_L2, Real.dist_eq]
  · simp

private noncomputable def extended : KleinerLottApprox
    (⟨0, by norm_num⟩ : Icc (0 : ℝ) 2)
    (⟨0, by norm_num⟩ : Icc (0 : ℝ) (201 / 100)) (4 * (1 / 100)) :=
  (exactApprox (⟨0, by norm_num⟩ : Icc (0 : ℝ) 2)
    (ε := 1 / 100) (by norm_num) (by norm_num)).enlargeIntervalTarget
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem added_endpoint_covered :
    infDist (⟨201 / 100, by norm_num⟩ : Icc (0 : ℝ) (201 / 100))
      (extended.toFun '' ball (⟨0, by norm_num⟩ : Icc (0 : ℝ) 2) (4 * (1 / 100))⁻¹) ≤ 4 * (1 / 100) := by
  apply extended.coverage
  norm_num [Subtype.dist_eq, Real.dist_eq]

theorem extension_preserves_point_function (x : Icc (0 : ℝ) 2) :
    (extended.toFun x : ℝ) = (x : ℝ) := rfl

theorem composite_coverage_on_closed_buffer
    (z : WithLp 2 (ℝ × ℝ))
    (hz : dist z (WithLp.toLp 2 (0, 0)) ≤ 9 / 10) :
    ∃ x ∈ ball (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) 1,
      dist x z < 3 / 50 ∧ dist x (WithLp.toLp 2 (0, 0)) <
        dist z (WithLp.toLp 2 (0, 0)) + 3 / 50 := by
  let f := exactApprox (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)))
    (ε := 1 / 100) (by norm_num) (by norm_num)
  let g := exactApprox (0 : ℝ) (ε := 1 / 100) (by norm_num) (by norm_num)
  have h := f.product_factor_composition_estimates g (S := 1) (by norm_num)
  obtain ⟨x, hx, hd, hr⟩ := h.2 z (by linarith)
  change dist x z < 3 * (1 / 100 + 1 / 100) at hd
  norm_num at hd hr
  exact ⟨x, hx, hd, hr⟩

#print axioms composite_coverage_on_closed_buffer
#print axioms exact_cross_has_negative_height
#print axioms repeated_antipodes_need_cross_distances
#print axioms added_endpoint_covered
#print axioms extension_preserves_point_function
end EdgeRegression
