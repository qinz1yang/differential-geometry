import DifferentialGeometry.Geometry.Metric.Approximation.MarkedIntervalTargetRescaling
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Set Metric GC.MetricGeometry

namespace MarkedIntervalRegression

private abbrev Interval := Icc (0 : ℝ) 1000
private noncomputable def oldPoint : Interval := ⟨1 / 10, by norm_num⟩
private noncomputable def newPoint : Interval := ⟨1 / 1000000, by norm_num⟩

private noncomputable def intervalMap : KleinerLottApprox oldPoint oldPoint (1 / 1000000) :=
  (IsometryEquiv.refl Interval).toKleinerLottApprox rfl (by norm_num) (by norm_num)

theorem actual_marked_interval_rescales_and_repairs :
    let : MetricSpace Interval := (inferInstance : MetricSpace Interval).rescale (3 / 4) (by norm_num)
    ∃ g : KleinerLottApprox newPoint (⟨0, by norm_num⟩ : Icc (0 : ℝ) 750) (1 / 200),
      (g.toFun newPoint).val = 0 ∧
      (g.toFun ⟨100, by norm_num⟩).val = 75 ∧
      (g.toFun ⟨1000, by norm_num⟩).val = 750 := by
  have hh := intervalMap.exists_strong_edge_interval_model newPoint (Δ := 1) (δ := 1 / 200)
    (e := 1 / 1000000) (θ := 0) (c := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [oldPoint, newPoint, Subtype.dist_eq, Real.dist_eq])
    (by norm_num [oldPoint]) (by norm_num) (by norm_num)
    (by change (1 / 1000000 : ℝ) ≤ 2 * (1 / 1000000) + 0; norm_num)
  dsimp only at hh
  rw [show (3 / 4 : ℝ) * 1000 = 750 by norm_num] at hh
  let : MetricSpace Interval := (inferInstance : MetricSpace Interval).rescale (3 / 4) (by norm_num)
  obtain ⟨hD, g, _, hg, hv⟩ := hh
  refine ⟨g, congrArg Subtype.val hg, ?_, ?_⟩
  · have he := hv ⟨100, by norm_num⟩
      (by intro h; have := congrArg Subtype.val h; norm_num [newPoint] at this)
    change _ = (3 / 4) * (100 : ℝ) at he
    norm_num at he
    exact he
  · have he := hv ⟨1000, by norm_num⟩
      (by intro h; have := congrArg Subtype.val h; norm_num [newPoint] at this)
    change _ = (3 / 4) * (1000 : ℝ) at he
    norm_num at he
    exact he

end MarkedIntervalRegression

#print axioms MarkedIntervalRegression.actual_marked_interval_rescales_and_repairs
