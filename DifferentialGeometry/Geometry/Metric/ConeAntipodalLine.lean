import DifferentialGeometry.Geometry.Metric.EuclideanCone

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal

namespace Metric.EuclideanCone

variable {Y : Type*}

def twoRayPath (a b : Y) (t : ℝ) : EuclideanCone Y :=
  if 0 ≤ t then mk t.toNNReal a else mk (-t).toNNReal b

@[simp] theorem twoRayPath_coe (a b : Y) (r : ℝ≥0) :
    twoRayPath a b r = mk r a := by
  rw [twoRayPath, ite_eq_left (show (0 : ℝ) ≤ r from r.property), Real.toNNReal_coe]

@[simp] theorem twoRayPath_neg_coe (a b : Y) (r : ℝ≥0) :
    twoRayPath a b (-r) = mk r b := by
  by_cases hr : r = 0
  · subst r
    simp [twoRayPath]
  · have hpos : 0 < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
    simp only [twoRayPath, ite_eq_right (by linarith : ¬ 0 ≤ -(r : ℝ)), neg_neg,
      Real.toNNReal_coe]

@[simp] theorem twoRayPath_zero (a b : Y) : twoRayPath a b 0 = tip := by
  simp [twoRayPath]

variable [MetricSpace Y]

theorem dist_mk_eq_add_of_pi_le {a b : Y} (hab : Real.pi ≤ dist a b) (r s : ℝ≥0) :
    dist (mk r a) (mk s b) = (r : ℝ) + s := by
  rw [dist_mk]
  unfold coneDistance
  rw [min_eq_left hab, Real.cos_pi]
  rw [show (r : ℝ) ^ 2 + (s : ℝ) ^ 2 - 2 * r * s * (-1) =
      ((r : ℝ) + s) ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ r + s by positivity)]

theorem isometry_twoRayPath_iff {a b : Y} :
    Isometry (twoRayPath a b) ↔ Real.pi ≤ dist a b := by
  constructor
  · intro h
    have hd := h.dist_eq (1 : ℝ) (-1)
    have hp : twoRayPath a b (1 : ℝ) = mk 1 a := twoRayPath_coe a b 1
    have hm : twoRayPath a b (-1 : ℝ) = mk 1 b := twoRayPath_neg_coe a b 1
    rw [hp, hm, Real.dist_eq] at hd
    norm_num at hd
    have hs := coneDistance_sq (x := ((1 : ℝ), a)) (y := ((1 : ℝ), b))
      (by norm_num) (by norm_num)
    have hd' : coneDistance ((1 : ℝ), a) ((1 : ℝ), b) = 2 := by
      simpa only [dist_mk, NNReal.coe_one] using hd
    rw [hd'] at hs
    have he : min Real.pi (dist a b) = Real.pi :=
      Real.injOn_cos ⟨le_min Real.pi_pos.le dist_nonneg, min_le_left _ _⟩
        ⟨Real.pi_pos.le, le_rfl⟩ (by rw [Real.cos_pi]; dsimp at hs; nlinarith)
    exact le_trans (le_of_eq he.symm) (min_le_right _ _)
  · intro hab
    apply Isometry.of_dist_eq
    intro s t
    rw [Real.dist_eq]
    by_cases hs : 0 ≤ s
    · by_cases ht : 0 ≤ t
      · simp only [twoRayPath, ite_eq_left hs, ite_eq_left ht, dist_mk, coneDistance_same_direction,
          Real.coe_toNNReal s hs, Real.coe_toNNReal t ht]
      · rw [twoRayPath, ite_eq_left hs, twoRayPath, ite_eq_right ht, dist_mk_eq_add_of_pi_le hab,
          Real.coe_toNNReal s hs, Real.coe_toNNReal (-t) (by linarith)]
        rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
        ring
    · by_cases ht : 0 ≤ t
      · rw [twoRayPath, ite_eq_right hs, twoRayPath, ite_eq_left ht,
          dist_mk_eq_add_of_pi_le (by simpa only [dist_comm] using hab),
          Real.coe_toNNReal (-s) (by linarith), Real.coe_toNNReal t ht]
        rw [abs_of_nonpos (by linarith : s - t ≤ 0)]
        ring
      · simp only [twoRayPath, ite_eq_right hs, ite_eq_right ht, dist_mk, coneDistance_same_direction,
          Real.coe_toNNReal (-s) (by linarith : 0 ≤ -s),
          Real.coe_toNNReal (-t) (by linarith : 0 ≤ -t)]
        rw [show -s - -t = -(s - t) by ring, abs_neg]

end Metric.EuclideanCone
