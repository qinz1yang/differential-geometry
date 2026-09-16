import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform

open scoped NNReal

namespace Metric

variable {X : Type*} [SeminormedAddGroup X]

def closedBallTranslate (h : X) {r R : ℝ} (hR : ‖h‖ + r ≤ R) :
    closedBall (0 : X) r → closedBall (0 : X) R := fun z =>
  ⟨h + z, by
    rw [mem_closedBall, dist_zero_right]
    have hz : ‖(z : X)‖ ≤ r := by
      simpa only [mem_closedBall, dist_zero_right] using z.property
    exact (norm_add_le _ _).trans ((add_le_add le_rfl hz).trans hR)⟩

@[simp] theorem closedBallTranslate_coe (h : X) {r R : ℝ} (hR : ‖h‖ + r ≤ R)
    (z : closedBall (0 : X) r) : (closedBallTranslate h hR z : X) = h + z := rfl

theorem isometry_closedBallTranslate (h : X) {r R : ℝ} (hR : ‖h‖ + r ≤ R) :
    Isometry (closedBallTranslate h hR) := by
  apply Isometry.of_dist_eq
  intro z w
  simp only [Subtype.dist_eq, closedBallTranslate_coe, dist_add_left]

end Metric

namespace LipschitzWith

variable {X Y T : Type*} [SeminormedAddGroup X] [PseudoMetricSpace Y]
  [PseudoMetricSpace T] {r R : ℝ} {C : ℝ≥0}
  {N : T × Metric.closedBall (0 : X) R → Y}

theorem prod_precomp_closedBallTranslate (hN : LipschitzWith C N)
    (h : X) (hR : ‖h‖ + r ≤ R) :
    LipschitzWith C
      (fun p : T × Metric.closedBall (0 : X) r => N (p.1, Metric.closedBallTranslate h hR p.2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [Prod.dist_eq, Subtype.dist_eq, Metric.closedBallTranslate_coe,
    dist_add_left] using
    hN.dist_le_mul (p.1, Metric.closedBallTranslate h hR p.2)
      (q.1, Metric.closedBallTranslate h hR q.2)

theorem time_precomp_closedBallTranslate (hN : LipschitzWith C N)
    (h : X) (hR : ‖h‖ + r ≤ R) (t : T) :
    LipschitzWith C
      (fun z : Metric.closedBall (0 : X) r => N (t, Metric.closedBallTranslate h hR z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [Prod.dist_eq, dist_self, Subtype.dist_eq, Metric.closedBallTranslate_coe,
    dist_add_left, max_eq_right dist_nonneg] using
    hN.dist_le_mul (t, Metric.closedBallTranslate h hR z)
      (t, Metric.closedBallTranslate h hR w)

end LipschitzWith

namespace LipschitzWith

variable {X Y : Type*} [SeminormedAddGroup X] [SeminormedAddCommGroup Y]
  {r R : ℝ} {C : ℝ≥0} {N : ℝ × Metric.closedBall (0 : X) R → Y}

theorem norm_sub_origin_time_precomp_closedBallTranslate (hN : LipschitzWith C N)
    (h : X) (hh : ‖h‖ ≤ r) (hr : 0 ≤ r) (hR : 2 * r ≤ R)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) r) (z : Metric.closedBall (0 : X) r) :
    ‖N (t, Metric.closedBallTranslate h
      ((add_le_add hh le_rfl).trans (by simpa only [two_mul] using hR)) z) -
      N (0, ⟨0, Metric.mem_closedBall_self ((mul_nonneg zero_le_two hr).trans hR)⟩)‖ ≤
      C * (2 * r) := by
  have hz : ‖(z : X)‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  have hsp : ‖h + (z : X)‖ ≤ 2 * r := by
    simpa only [two_mul] using (norm_add_le _ _).trans (add_le_add hh hz)
  have htime : |t| ≤ 2 * r := by
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans (le_mul_of_one_le_left hr (by norm_num))
  have hdist := hN.dist_le_mul
    (t, Metric.closedBallTranslate h
      ((add_le_add hh le_rfl).trans (by simpa only [two_mul] using hR)) z)
    (0, ⟨0, Metric.mem_closedBall_self ((mul_nonneg zero_le_two hr).trans hR)⟩)
  have hn : ‖N (t, Metric.closedBallTranslate h
      ((add_le_add hh le_rfl).trans (by simpa only [two_mul] using hR)) z) -
      N (0, ⟨0, Metric.mem_closedBall_self ((mul_nonneg zero_le_two hr).trans hR)⟩)‖ ≤
      C * max |t| ‖h + (z : X)‖ := by
    simpa only [Prod.dist_eq, Subtype.dist_eq, Metric.closedBallTranslate_coe,
      dist_zero_right, dist_eq_norm, sub_zero, Real.norm_eq_abs] using hdist
  exact hn.trans (mul_le_mul_of_nonneg_left (max_le htime hsp) C.coe_nonneg)

end LipschitzWith

namespace LipschitzWith

variable {X Y T : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
  [PseudoMetricSpace T] {r R : ℝ} {C : ℝ≥0}
  {N : T × Metric.closedBall (0 : X) R → Y}

theorem norm_sub_time_closedBallTranslate (hN : LipschitzWith C N)
    (h k : X) (hh : ‖h‖ + r ≤ R) (hk : ‖k‖ + r ≤ R)
    (t : T) (z : Metric.closedBall (0 : X) r) :
    ‖N (t, Metric.closedBallTranslate h hh z) - N (t, Metric.closedBallTranslate k hk z)‖ ≤
      C * ‖h - k‖ := by
  simpa only [Prod.dist_eq, dist_self, Subtype.dist_eq, Metric.closedBallTranslate_coe,
    dist_add_right, max_eq_right dist_nonneg, dist_eq_norm,
    add_sub_add_right_eq_sub, max_eq_right (norm_nonneg _)] using
    hN.dist_le_mul (t, Metric.closedBallTranslate h hh z)
      (t, Metric.closedBallTranslate k hk z)

end LipschitzWith
