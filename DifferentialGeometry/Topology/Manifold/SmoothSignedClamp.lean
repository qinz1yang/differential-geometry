/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open Set Topology
open scoped ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology

def signedClampBump (a : ℝ) (ha : 0 < a) : ContDiffBump (0 : ℝ) where
  rIn := a / 3
  rOut := 2 * a / 3
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def smoothSignedClamp (a : ℝ) (ha : 0 < a) (t : ℝ) : ℝ :=
  t * signedClampBump a ha t +
    Real.smoothTransition ((t - a / 3) / (a / 3)) -
      Real.smoothTransition ((-t - a / 3) / (a / 3))

theorem contDiff_smoothSignedClamp (a : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (smoothSignedClamp a ha) := by
  unfold smoothSignedClamp
  have hpos : ContDiff ℝ ∞ (fun t : ℝ =>
      Real.smoothTransition ((t - a / 3) / (a / 3))) :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const (a / 3))
  have hneg : ContDiff ℝ ∞ (fun t : ℝ =>
      Real.smoothTransition ((-t - a / 3) / (a / 3))) :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_id.neg.sub contDiff_const).div_const (a / 3))
  exact ((contDiff_id.mul (signedClampBump a ha).contDiff).add hpos).sub hneg

theorem smoothSignedClamp_eq_self_of_abs_le_third
    (a : ℝ) (ha : 0 < a) {t : ℝ} (ht : |t| ≤ a / 3) :
    smoothSignedClamp a ha t = t := by
  have ht_mem : t ∈ Metric.closedBall (0 : ℝ) (signedClampBump a ha).rIn := by
    simpa [signedClampBump, Real.dist_eq] using ht
  have hpos : (t - a / 3) / (a / 3) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_trans (le_abs_self t) ht)) (by positivity)
  have hneg : (-t - a / 3) / (a / 3) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rw [sub_nonpos]
    exact le_trans (neg_le_abs t) ht
  simp [smoothSignedClamp, (signedClampBump a ha).one_of_mem_closedBall ht_mem,
    Real.smoothTransition.zero_of_nonpos hpos,
    Real.smoothTransition.zero_of_nonpos hneg]

theorem smoothSignedClamp_eq_one_of_two_thirds_le
    (a : ℝ) (ha : 0 < a) {t : ℝ} (ht : 2 * a / 3 ≤ t) :
    smoothSignedClamp a ha t = 1 := by
  have hb : signedClampBump a ha t = 0 := by
    apply (signedClampBump a ha).zero_of_le_dist
    simpa [signedClampBump, Real.dist_eq, abs_of_nonneg (le_trans (by positivity) ht)] using ht
  have hpos : 1 ≤ (t - a / 3) / (a / 3) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hneg : (-t - a / 3) / (a / 3) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    linarith
  simp [smoothSignedClamp, hb, Real.smoothTransition.one_of_one_le hpos,
    Real.smoothTransition.zero_of_nonpos hneg]

theorem smoothSignedClamp_neg (a : ℝ) (ha : 0 < a) (t : ℝ) :
    smoothSignedClamp a ha (-t) = -smoothSignedClamp a ha t := by
  unfold smoothSignedClamp
  rw [(signedClampBump a ha).neg]
  simp only [neg_neg]
  ring

theorem smoothSignedClamp_eq_neg_one_of_le_neg_two_thirds
    (a : ℝ) (ha : 0 < a) {t : ℝ} (ht : t ≤ -(2 * a / 3)) :
    smoothSignedClamp a ha t = -1 := by
  rw [show t = -(-t) by ring, smoothSignedClamp_neg]
  rw [smoothSignedClamp_eq_one_of_two_thirds_le a ha (by linarith)]

theorem smoothSignedClamp_pos_of_pos
    (a : ℝ) (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    0 < smoothSignedClamp a ha t := by
  rcases le_or_gt (2 * a / 3) t with houter | hinner
  · rw [smoothSignedClamp_eq_one_of_two_thirds_le a ha houter]
    norm_num
  · have hb : 0 < signedClampBump a ha t := by
      apply (signedClampBump a ha).pos_of_mem_ball
      simpa [signedClampBump, Real.dist_eq, abs_of_pos ht] using hinner
    have hneg : Real.smoothTransition ((-t - a / 3) / (a / 3)) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      linarith
    have htransition : 0 ≤ Real.smoothTransition ((t - a / 3) / (a / 3)) :=
      Real.smoothTransition.nonneg _
    unfold smoothSignedClamp
    rw [hneg]
    nlinarith

theorem smoothSignedClamp_neg_of_neg
    (a : ℝ) (ha : 0 < a) {t : ℝ} (ht : t < 0) :
    smoothSignedClamp a ha t < 0 := by
  rw [show t = -(-t) by ring, smoothSignedClamp_neg]
  exact neg_neg_of_pos (smoothSignedClamp_pos_of_pos a ha (by linarith))

theorem smoothSignedClamp_pos_iff (a : ℝ) (ha : 0 < a) (t : ℝ) :
    0 < smoothSignedClamp a ha t ↔ 0 < t := by
  constructor
  · intro hclamp
    by_contra hnot
    have ht : t ≤ 0 := le_of_not_gt hnot
    rcases ht.eq_or_lt with rfl | ht
    · have hzero := smoothSignedClamp_eq_self_of_abs_le_third a ha
          (t := 0) (by simpa only [abs_zero] using (show 0 ≤ a / 3 by positivity))
      linarith
    · linarith [smoothSignedClamp_neg_of_neg a ha ht]
  · exact smoothSignedClamp_pos_of_pos a ha

theorem smoothSignedClamp_neg_iff (a : ℝ) (ha : 0 < a) (t : ℝ) :
    smoothSignedClamp a ha t < 0 ↔ t < 0 := by
  calc
    smoothSignedClamp a ha t < 0 ↔ 0 < -smoothSignedClamp a ha t := neg_pos.symm
    _ ↔ 0 < smoothSignedClamp a ha (-t) := by rw [smoothSignedClamp_neg]
    _ ↔ 0 < -t := smoothSignedClamp_pos_iff a ha (-t)
    _ ↔ t < 0 := neg_pos

theorem smoothSignedClamp_nonpos_iff (a : ℝ) (ha : 0 < a) (t : ℝ) :
    smoothSignedClamp a ha t ≤ 0 ↔ t ≤ 0 := by
  simpa only [not_lt] using not_congr (smoothSignedClamp_pos_iff a ha t)

theorem smoothSignedClamp_eq_zero_iff (a : ℝ) (ha : 0 < a) (t : ℝ) :
    smoothSignedClamp a ha t = 0 ↔ t = 0 := by
  constructor
  · intro hzero
    apply le_antisymm
    · exact (smoothSignedClamp_nonpos_iff a ha t).mp hzero.le
    · have : smoothSignedClamp a ha (-t) ≤ 0 := by
        rw [smoothSignedClamp_neg, neg_nonpos]
        exact hzero.ge
      linarith [(smoothSignedClamp_nonpos_iff a ha (-t)).mp this]
  · rintro rfl
    exact smoothSignedClamp_eq_self_of_abs_le_third a ha
      (by simpa only [abs_zero] using (show 0 ≤ a / 3 by positivity))

theorem hasDerivAt_smoothSignedClamp_zero (a : ℝ) (ha : 0 < a) :
    HasDerivAt (smoothSignedClamp a ha) 1 0 := by
  apply (hasDerivAt_id (x := (0 : ℝ))).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show 0 < a / 3 by positivity)] with t ht
  apply smoothSignedClamp_eq_self_of_abs_le_third a ha
  have habs : |t| < a / 3 := by simpa [Real.dist_eq] using ht
  exact habs.le

end DifferentialGeometry.Topology
