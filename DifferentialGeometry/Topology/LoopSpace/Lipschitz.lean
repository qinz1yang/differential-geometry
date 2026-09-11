import DifferentialGeometry.Topology.LoopSpace.Basic
import Mathlib.Analysis.Normed.Group.Quotient



noncomputable section

open Function
open scoped ENNReal NNReal

namespace DifferentialGeometry.Topology

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
