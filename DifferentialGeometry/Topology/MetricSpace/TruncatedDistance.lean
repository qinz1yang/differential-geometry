import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Group.Real

section

set_option autoImplicit false
noncomputable section

open scoped ENNReal NNReal

namespace EMetric

variable {X : Type*} [PseudoEMetricSpace X]

theorem lipschitzWith_truncated_edist (p : X) :
    LipschitzWith 1 (fun x => (min (edist x p) 1).toReal) := by
  intro x y
  rw [ENNReal.coe_one, one_mul]
  change edist ((min (edist x p) 1).toReal) ((min (edist y p) 1).toReal) ≤ edist x y
  by_cases hxy : edist x y = ⊤
  · rw [hxy]
    exact le_top
  by_cases hxp : edist x p = ⊤
  · have hyp : edist y p = ⊤ := by
      by_contra hyp
      have hfin := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hxy, hyp⟩)
        (edist_triangle x y p)
      exact hfin hxp
    rw [hxp, hyp, edist_self]
    exact zero_le
  · have hyp : edist y p ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
        ⟨by simpa only [edist_comm y x] using hxy, hxp⟩) (edist_triangle y x p)
    have hmin := (LipschitzWith.id (α := ℝ)).min_const 1
    have h := hmin (edist x p).toReal (edist y p).toReal
    simp only [ENNReal.coe_one, one_mul] at h
    rw [ENNReal.toReal_min hxp (by simp), ENNReal.toReal_min hyp (by simp),
      ENNReal.toReal_one]
    apply h.trans
    rw [edist_dist, Real.dist_eq]
    have hx := ENNReal.toReal_le_add (edist_triangle x y p) hxy hyp
    have hy := ENNReal.toReal_le_add (edist_triangle y x p)
      (by simpa only [edist_comm y x] using hxy) hxp
    rw [edist_comm y x] at hy
    have habs : |(edist x p).toReal - (edist y p).toReal| ≤ (edist x y).toReal :=
      abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    exact (ENNReal.ofReal_le_ofReal habs).trans ENNReal.ofReal_toReal_le

theorem norm_truncated_edist_le_one (x p : X) : ‖(min (edist x p) 1).toReal‖ ≤ (1 : ℝ) := by
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have h : (min (edist x p) 1).toReal ≤ (1 : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono (by simp) (min_le_right _ _)
  simpa only [ENNReal.toReal_one] using h

end EMetric

end

end
