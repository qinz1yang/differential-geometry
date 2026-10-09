import DifferentialGeometry.Analysis.Calculus.Taylor.QuadraticBound
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- A vanishing slope derivative gives a quadratic slope bound while allowing
linear dependence on the remaining variables. The same neighborhood controls
both the full derivative and its slope restriction. -/
theorem exists_local_bounds_of_vanishing_slope_derivative
    {F : X × Y → Z} {a : X} (hF : ContDiffAt ℝ 2 F (a, 0))
    (hzero : (fderiv ℝ F (a, 0)).comp (ContinuousLinearMap.inr ℝ X Y) = 0) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < C ∧ ∀ q ∈ ball (a, (0 : Y)) r,
      ‖F q - F (a, 0)‖ ≤ C * (‖q.1 - a‖ + ‖q.2‖ ^ 2) ∧
      ‖fderiv ℝ F q‖ ≤ C ∧
      ‖(fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ X Y)‖ ≤
        C * ‖q - (a, 0)‖ := by
  let M : ℝ := ‖iteratedFDeriv ℝ 2 F (a, 0)‖ + 1
  let N : ℝ := ‖fderiv ℝ F (a, 0)‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hD : ContDiffAt ℝ 1 (fderiv ℝ F) (a, 0) :=
    hF.fderiv_right (by norm_num)
  obtain ⟨K, S, hS, hLip⟩ := hD.exists_lipschitzOnWith
  have hiter : ContinuousAt (iteratedFDeriv ℝ 2 F) (a, (0 : Y)) :=
    hF.continuousAt_iteratedFDeriv (by norm_num)
  have hMnear : ∀ᶠ q in 𝓝 (a, (0 : Y)), ‖iteratedFDeriv ℝ 2 F q‖ < M :=
    hiter.norm.eventually
      (gt_mem_nhds (by dsimp [M]; linarith))
  have hNnear : ∀ᶠ q in 𝓝 (a, (0 : Y)), ‖fderiv ℝ F q‖ < N :=
    hD.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [N]; linarith))
  have hnear : ∀ᶠ q in 𝓝 (a, (0 : Y)),
      ContDiffAt ℝ 2 F q ∧ ‖iteratedFDeriv ℝ 2 F q‖ ≤ M ∧
        ‖fderiv ℝ F q‖ ≤ N ∧ q ∈ S := by
    filter_upwards [hF.eventually (by norm_num), hMnear, hNnear, hS] with q hq hMq hNq hSq
    exact ⟨hq, hMq.le, hNq.le, hSq⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r : ℝ := min ε 1
  have hr : 0 < r := lt_min hε zero_lt_one
  have hrε : r ≤ ε := min_le_left _ _
  have hr1 : r ≤ 1 := min_le_right _ _
  have hlocal (q : X × Y) (hq : q ∈ ball (a, (0 : Y)) r) :
      ContDiffAt ℝ 2 F q ∧ ‖iteratedFDeriv ℝ 2 F q‖ ≤ M ∧
        ‖fderiv ℝ F q‖ ≤ N ∧ q ∈ S :=
    hball (ball_subset_ball hrε hq)
  have hbase : (a, (0 : Y)) ∈ ball (a, (0 : Y)) r := mem_ball_self hr
  have hbaseS : (a, (0 : Y)) ∈ S := (hlocal _ hbase).2.2.2
  let C : ℝ := M + N + K + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hNC : N ≤ C := by dsimp [C]; linarith [K.coe_nonneg]
  have hKC : (K : ℝ) ≤ C := by dsimp [C]; linarith
  refine ⟨r, C, hr, hr1, hC, ?_⟩
  intro q hq
  have hq0 : ‖q - (a, (0 : Y))‖ < r := by simpa only [mem_ball, dist_eq_norm] using hq
  have hfst : ‖q.1 - a‖ ≤ ‖q - (a, (0 : Y))‖ := by
    simpa only [Prod.fst_sub] using (norm_fst_le (q - (a, (0 : Y))))
  have hx : ‖q.1 - a‖ ≤ 1 := (hfst.trans hq0.le).trans hr1
  have hsq : ‖q - (a, (0 : Y))‖ ^ 2 ≤ ‖q.1 - a‖ + ‖q.2‖ ^ 2 := by
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_zero]
    rcases le_total ‖q.1 - a‖ ‖q.2‖ with hxy | hyx
    · rw [max_eq_right hxy]
      linarith [norm_nonneg (q.1 - a)]
    · rw [max_eq_left hyx]
      nlinarith [norm_nonneg (q.1 - a), sq_nonneg ‖q.2‖]
  have hvertical (y : Y) : fderiv ℝ F (a, 0) (0, y) = 0 := by
    have h := congrArg (fun L : Y →L[ℝ] Z => L y) hzero
    simpa using h
  have hlinear : fderiv ℝ F (a, 0) (q - (a, 0)) =
      fderiv ℝ F (a, 0) (q.1 - a, 0) := by
    rw [show q - (a, (0 : Y)) = (q.1 - a, 0) + (0, q.2) by ext <;> simp,
      map_add, hvertical, add_zero]
  have hlin : ‖fderiv ℝ F (a, 0) (q - (a, 0))‖ ≤ N * ‖q.1 - a‖ := by
    rw [hlinear]
    calc
      _ ≤ ‖fderiv ℝ F (a, 0)‖ * ‖(q.1 - a, (0 : Y))‖ :=
        (fderiv ℝ F (a, 0)).le_opNorm _
      _ ≤ N * ‖q.1 - a‖ := by
        simpa using mul_le_mul_of_nonneg_right (hlocal _ hbase).2.2.1 (norm_nonneg (q.1 - a))
  have hrem := norm_sub_sub_fderiv_le_of_contDiffOn isOpen_ball (convex_ball _ _)
    (fun z hz => (hlocal z hz).1.contDiffWithinAt)
    (fun z hz => (hlocal z hz).2.1) hbase hq
  have hvalue : ‖F q - F (a, 0)‖ ≤ C * (‖q.1 - a‖ + ‖q.2‖ ^ 2) := by
    calc
      _ ≤ ‖F q - F (a, 0) - fderiv ℝ F (a, 0) (q - (a, 0))‖ +
          ‖fderiv ℝ F (a, 0) (q - (a, 0))‖ := by
        simpa only [add_comm] using norm_le_norm_add_norm_sub'
          (F q - F (a, 0)) (fderiv ℝ F (a, 0) (q - (a, 0)))
      _ ≤ M / 2 * ‖q - (a, 0)‖ ^ 2 + N * ‖q.1 - a‖ := add_le_add hrem hlin
      _ ≤ M / 2 * (‖q.1 - a‖ + ‖q.2‖ ^ 2) + N * ‖q.1 - a‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hsq (show 0 ≤ M / 2 by positivity)) le_rfl
      _ ≤ C * (‖q.1 - a‖ + ‖q.2‖ ^ 2) := by
        dsimp [C]
        nlinarith [norm_nonneg (q.1 - a), sq_nonneg ‖q.2‖, K.coe_nonneg,
          mul_nonneg hM.le (norm_nonneg (q.1 - a)),
          mul_nonneg hM.le (sq_nonneg ‖q.2‖),
          mul_nonneg hN.le (sq_nonneg ‖q.2‖),
          mul_nonneg K.coe_nonneg (norm_nonneg (q.1 - a)),
          mul_nonneg K.coe_nonneg (sq_nonneg ‖q.2‖)]
  refine ⟨hvalue, (hlocal _ hq).2.2.1.trans hNC, ?_⟩
  have hdiff : ‖fderiv ℝ F q - fderiv ℝ F (a, 0)‖ ≤
      (K : ℝ) * ‖q - (a, 0)‖ := by
    simpa only [dist_eq_norm] using hLip.dist_le_mul q (hlocal _ hq).2.2.2 (a, 0) hbaseS
  have heq : (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ X Y) =
      (fderiv ℝ F q - fderiv ℝ F (a, 0)).comp (ContinuousLinearMap.inr ℝ X Y) := by
    rw [ContinuousLinearMap.sub_comp, hzero, sub_zero]
  rw [heq]
  calc
    _ ≤ ‖fderiv ℝ F q - fderiv ℝ F (a, 0)‖ * ‖ContinuousLinearMap.inr ℝ X Y‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ F q - fderiv ℝ F (a, 0)‖ := by
      exact mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ X Y)
    _ ≤ (K : ℝ) * ‖q - (a, 0)‖ := hdiff
    _ ≤ C * ‖q - (a, 0)‖ := mul_le_mul_of_nonneg_right hKC (norm_nonneg _)

end DifferentialGeometry.Analysis
