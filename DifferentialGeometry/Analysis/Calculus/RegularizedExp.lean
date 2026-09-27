import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

namespace Real

noncomputable def regularizedExp (r : ℝ) : ℝ :=
  if r < log (1 / 2) then 1 / 2 + (1 / 2) * (r - log (1 / 2))
  else if log (3 / 2) < r then 3 / 2 + (3 / 2) * (r - log (3 / 2))
  else exp r

private theorem log_half_le_log_three_halves : log (1 / 2 : ℝ) ≤ log (3 / 2 : ℝ) :=
  log_le_log (by norm_num) (by norm_num)

theorem regularizedExp_eq_exp {x : ℝ}
    (hx : x ∈ Set.Icc (log (1 / 2 : ℝ)) (log (3 / 2 : ℝ))) :
    regularizedExp x = exp x := by
  rw [regularizedExp, if_neg (not_lt.mpr hx.1), if_neg (not_lt.mpr hx.2)]

theorem regularizedExp_of_le {x : ℝ} (hx : x ≤ log (1 / 2 : ℝ)) :
    regularizedExp x = 1 / 2 + (1 / 2) * (x - log (1 / 2)) := by
  rcases hx.lt_or_eq with hx | rfl
  · rw [regularizedExp, if_pos hx]
  · rw [regularizedExp, if_neg (lt_irrefl _),
      if_neg (not_lt.mpr log_half_le_log_three_halves)]
    rw [exp_log (by norm_num : 0 < (1 / 2 : ℝ))]
    ring

theorem regularizedExp_of_ge {x : ℝ} (hx : log (3 / 2 : ℝ) ≤ x) :
    regularizedExp x = 3 / 2 + (3 / 2) * (x - log (3 / 2)) := by
  rcases hx.lt_or_eq with hx | hx
  · rw [regularizedExp, if_neg (not_lt.mpr (log_half_le_log_three_halves.trans hx.le)),
      if_pos hx]
  · subst x
    rw [regularizedExp, if_neg (not_lt.mpr log_half_le_log_three_halves),
      if_neg (lt_irrefl _), exp_log (by norm_num : 0 < (3 / 2 : ℝ))]
    ring

private theorem exp_sub_bounds {x y : ℝ}
    (hx : log (1 / 2 : ℝ) ≤ x) (hxy : x ≤ y) (hy : y ≤ log (3 / 2 : ℝ)) :
    (1 / 2) * (y - x) ≤ exp y - exp x ∧
      exp y - exp x ≤ (3 / 2) * (y - x) := by
  have hm : ∀ z ∈ interior (Set.Icc x y),
      (1 / 2 : ℝ) ≤ deriv exp z ∧ deriv exp z ≤ 3 / 2 := by
    intro z hz
    have hz' := interior_subset hz
    rw [deriv_exp]
    constructor
    · calc (1 / 2 : ℝ) = exp (log (1 / 2 : ℝ)) := (exp_log (by norm_num)).symm
           _ ≤ exp z := exp_le_exp.mpr (hx.trans hz'.1)
    · calc exp z ≤ exp (log (3 / 2 : ℝ)) := exp_le_exp.mpr (hz'.2.trans hy)
           _ = 3 / 2 := exp_log (by norm_num)
  constructor
  · exact (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv continuous_exp.continuousOn
      differentiable_exp.differentiableOn (fun z hz => (hm z hz).1)
      x (Set.left_mem_Icc.mpr hxy) y (Set.right_mem_Icc.mpr hxy) hxy
  · exact (convex_Icc x y).image_sub_le_mul_sub_of_deriv_le continuous_exp.continuousOn
      differentiable_exp.differentiableOn (fun z hz => (hm z hz).2)
      x (Set.left_mem_Icc.mpr hxy) y (Set.right_mem_Icc.mpr hxy) hxy

theorem regularizedExp_sub_bounds {x y : ℝ} (hxy : x ≤ y) :
    (1 / 2) * (y - x) ≤ regularizedExp y - regularizedExp x ∧
      regularizedExp y - regularizedExp x ≤ (3 / 2) * (y - x) := by
  rcases le_or_gt x (log (1 / 2 : ℝ)) with hx | hx
  · rw [regularizedExp_of_le hx]
    rcases le_or_gt y (log (1 / 2 : ℝ)) with hy | hy
    · rw [regularizedExp_of_le hy]
      constructor <;> linarith
    · rcases le_or_gt y (log (3 / 2 : ℝ)) with hyb | hyb
      · rw [regularizedExp_eq_exp ⟨hy.le, hyb⟩]
        obtain ⟨hlo, hup⟩ := exp_sub_bounds (x := log (1 / 2)) le_rfl hy.le hyb
        rw [exp_log (by norm_num : 0 < (1 / 2 : ℝ))] at hlo hup
        constructor <;> linarith
      · rw [regularizedExp_of_ge hyb.le]
        obtain ⟨hlo, hup⟩ := exp_sub_bounds (x := log (1 / 2)) (y := log (3 / 2))
          le_rfl log_half_le_log_three_halves le_rfl
        rw [exp_log (by norm_num : 0 < (1 / 2 : ℝ)),
          exp_log (by norm_num : 0 < (3 / 2 : ℝ))] at hlo hup
        constructor <;> linarith
  · rcases le_or_gt x (log (3 / 2 : ℝ)) with hxb | hxb
    · rw [regularizedExp_eq_exp ⟨hx.le, hxb⟩]
      rcases le_or_gt y (log (3 / 2 : ℝ)) with hyb | hyb
      · rw [regularizedExp_eq_exp ⟨hx.le.trans hxy, hyb⟩]
        exact exp_sub_bounds hx.le hxy hyb
      · rw [regularizedExp_of_ge hyb.le]
        obtain ⟨hlo, hup⟩ := exp_sub_bounds hx.le hxb (y := log (3 / 2)) le_rfl
        rw [exp_log (by norm_num : 0 < (3 / 2 : ℝ))] at hlo hup
        constructor <;> linarith
    · rw [regularizedExp_of_ge hxb.le, regularizedExp_of_ge (hxb.le.trans hxy)]
      constructor <;> linarith

@[simp]
theorem regularizedExp_zero : regularizedExp 0 = 1 := by
  rw [regularizedExp_eq_exp, exp_zero]
  constructor
  · exact log_nonpos (by norm_num) (by norm_num)
  · exact log_nonneg (by norm_num)

theorem regularizedExp_sub_one_sub_lipschitzWith :
    LipschitzWith (1 / 2) (fun r : ℝ => regularizedExp r - 1 - r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hbound : ∀ a b : ℝ, a ≤ b →
      |(regularizedExp b - 1 - b) - (regularizedExp a - 1 - a)| ≤ (1 / 2) * (b - a) := by
    intro a b hab
    have h := regularizedExp_sub_bounds hab
    apply abs_le.mpr
    constructor <;> linarith
  rcases le_total x y with hxy | hyx
  · rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), abs_sub_comm]
    norm_num
    simpa only [neg_sub] using hbound x y hxy
  · rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
    norm_num
    exact hbound y x hyx

end Real
