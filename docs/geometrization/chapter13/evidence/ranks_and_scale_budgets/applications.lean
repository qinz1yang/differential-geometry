import DifferentialGeometry.Geometry.Metric.Approximation.SplittingRank
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeRescalingBounds
import DifferentialGeometry.Geometry.Metric.Scaling.LipschitzScale
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open GC.MetricGeometry
namespace RankBudgetRegression

theorem zero_rank_does_not_use_zero_error {X : Type*} [MetricSpace X] (p : X) (N : ℕ) :
    splittingRank.{_, 0} p (fun _ => 0) N = 0 := by
  apply (splittingRank_zero_iff p (fun _ => 0) N).mpr
  intro k _ _ h
  obtain ⟨Y, mY, q, ⟨f⟩⟩ := h
  let := mY
  exact (lt_irrefl (0 : ℝ)) f.error_pos

theorem actual_rank_three {β : ℕ → ℝ} (hβ : 0 < β 3) (hβone : β 3 < 1) :
    splittingRank.{0, 0} (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 3)), (PUnit.unit : PUnit.{1}))) β 3 = 3 := by
  apply le_antisymm (splittingRank_le _ _ _) (le_splittingRank _ _ le_rfl ?_)
  exact ⟨PUnit.{1}, inferInstance, (PUnit.unit : PUnit.{1}),
    ⟨(IsometryEquiv.refl _).toKleinerLottApprox rfl hβ hβone⟩⟩

theorem real_zero_product : HasEuclideanSplitting.{0, 0} (7 : ℝ) 0 (1 / 10) :=
  hasEuclideanSplitting_zero 7 (ε := 1 / 10) (by norm_num) (by norm_num)

theorem contracted_scale_endpoint_budget :
    200 * (1 : ℝ) * (1 - (1 + 1 / 10 ^ 18 : ℝ)⁻¹) ≤ (1 / 10 ^ 8 : ℝ) / 100 ∧
    (101 : ℝ) + (1 / 10 ^ 8 : ℝ)⁻¹ / (1 + 1 / 10 ^ 18 : ℝ)⁻¹ +
      2 * (1 / 10 ^ 20) ≤ (1 / 10 ^ 20 : ℝ)⁻¹ := by
  have h := edge_recenter_rescale_budgets
    (Δ := 1) (Λ := 1 / 10 ^ 18) (q := 1 + 1 / 10 ^ 18)
    (b := 1 / 10 ^ 20) (s := 1 / 10 ^ 14) (b' := 1 / 10 ^ 8)
    (s' := 1 / 10 ^ 8) (R := 101) (D := 1 / 10 ^ 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.2.2.2.2.1, h.2.2.2.1⟩

#print axioms zero_rank_does_not_use_zero_error
#print axioms actual_rank_three
#print axioms real_zero_product
#print axioms contracted_scale_endpoint_budget
end RankBudgetRegression
