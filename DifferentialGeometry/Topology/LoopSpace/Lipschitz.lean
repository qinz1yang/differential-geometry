import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Analysis.Normed.Group.AddCircle



noncomputable section

open Function
open scoped ENNReal NNReal

namespace DifferentialGeometry.Topology

theorem exists_short_circle_lifts (x y : loopCircle) :
    ∃ a d : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ -(1 / 2 : ℝ) ≤ d ∧ d ≤ 1 / 2 ∧
      (a : loopCircle) = y ∧ ((a + d : ℝ) : loopCircle) = x ∧
      dist x y = |d| := by
  let a := AddCircle.equivIco (1 : ℝ) 0 y
  let d := AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) (x - y)
  have ha : 0 ≤ a.1 ∧ a.1 < 1 := by simpa using a.2
  have hd : -(1 / 2 : ℝ) ≤ d.1 ∧ d.1 < 1 / 2 := by convert d.2 using 1; norm_num
  have haq : (a.1 : loopCircle) = y := AddCircle.coe_equivIco
  have hdq : (d.1 : loopCircle) = x - y := AddCircle.coe_equivIco
  have hadq : ((a.1 + d.1 : ℝ) : loopCircle) = x := by
    rw [AddCircle.coe_add, haq, hdq]
    abel
  have hdabs : |d.1| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one, abs_le]
    exact ⟨hd.1, hd.2.le⟩
  have hnorm : ‖(d.1 : loopCircle)‖ = |d.1| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hdabs
  refine ⟨a.1, d.1, ha.1, ha.2.le, hd.1, hd.2.le, haq, hadq, ?_⟩
  rw [dist_eq_norm, ← hdq]
  exact hnorm

variable {Q : Type*} [PseudoEMetricSpace Q]



theorem loopCircle_projection_lipschitz : LipschitzWith 1 (fun t : ℝ => (t : loopCircle)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← QuotientAddGroup.mk_sub] using
    (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := x - y))




theorem loop_lipschitz_of_lift {γ : loopCircle → Q} {C : ℝ≥0}
    (hγ : LipschitzWith C (fun t : ℝ => γ (t : loopCircle))) : LipschitzWith C γ := by
  intro x y
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hb (z : ℝ) (hz : (z : loopCircle) = x - (b : loopCircle)) :
      edist (γ x) (γ (b : loopCircle)) ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖z‖ := by
    have hzb : ((z + b : ℝ) : loopCircle) = x := by
      rw [QuotientAddGroup.mk_add, hz, sub_add_cancel]
    simpa only [hzb, edist_dist, dist_eq_norm, add_sub_cancel_right] using
      hγ.edist_le_mul (z + b) b
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (x - (b : loopCircle))
  by_cases hC : C = 0
  · simpa only [hC, ENNReal.coe_zero, zero_mul] using hb z hz
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hC)
  have hfin : edist (γ x) (γ (b : loopCircle)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) (hb z hz)
  have hr : (edist (γ x) (γ (b : loopCircle))).toReal ≤ (C : ℝ) * ‖x - (b : loopCircle)‖ := by
    rw [mul_comm]
    apply (div_le_iff₀ hCpos).mp
    apply QuotientAddGroup.le_norm_iff.mpr
    intro a ha
    apply (div_le_iff₀ hCpos).mpr
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) (hb a ha)
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (norm_nonneg _), mul_comm] using h
  rw [edist_dist, dist_eq_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg,
    ← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hr

end DifferentialGeometry.Topology
