import DifferentialGeometry.Analysis.Calculus.Cutoff.SmoothTransition

/-!
The two-ball stereographic handle interpolation has exact inner and outer cap radius germs,
a positive derivative and a genuine inverse across the full interval of radii.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped ContDiff

namespace GC.GraphManifold.Assembly

def cycleHandleBlend (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

def cycleHandleRadius (t : ℝ) : ℝ :=
  (1 - cycleHandleBlend t) * (1 + t) + cycleHandleBlend t * (4 / (2 - t))

private theorem cycleHandleBlend_smooth : ContDiff ℝ ∞ cycleHandleBlend :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id |>.sub contDiff_const)

private theorem cycleHandleBlend_deriv_nonneg (t : ℝ) : 0 ≤ deriv cycleHandleBlend t := by
  apply Monotone.deriv_nonneg
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

private theorem cycleHandleBlend_bounds (t : ℝ) :
    0 ≤ cycleHandleBlend t ∧ cycleHandleBlend t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cycleHandleRadius_smooth : ContDiffOn ℝ ∞ cycleHandleRadius (Iio 2) := by
  unfold cycleHandleRadius
  refine ((contDiffOn_const.sub cycleHandleBlend_smooth.contDiffOn).mul
    (contDiffOn_const.add contDiffOn_id)).add ?_
  refine cycleHandleBlend_smooth.contDiffOn.mul (contDiffOn_const.div
    (contDiffOn_const.sub contDiffOn_id) ?_)
  intro t ht
  change 2 - t ≠ 0
  linarith [show t < 2 from ht]

private theorem cycleHandleRadius_deriv {t : ℝ} (ht : t < 2) :
    deriv cycleHandleRadius t =
      (1 - cycleHandleBlend t) + cycleHandleBlend t * (4 / (2 - t) ^ 2) +
        deriv cycleHandleBlend t * (4 / (2 - t) - (1 + t)) := by
  have hc := (cycleHandleBlend_smooth.differentiable (by simp) t).hasDerivAt
  have ha := (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
  have hb := (hasDerivAt_const t (4 : ℝ)).div
    ((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)) (by linarith : 2 - t ≠ 0)
  have hd := (((hasDerivAt_const t (1 : ℝ)).sub hc).mul ha).add (hc.mul hb)
  have he := hd.deriv
  change deriv cycleHandleRadius t = _ at he
  rw [he]
  dsimp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id_eq]
  ring

theorem cycleHandleRadius_deriv_pos {t : ℝ} (ht : t < 2) :
    0 < deriv cycleHandleRadius t := by
  rw [cycleHandleRadius_deriv ht]
  have hd : 0 < 2 - t := by linarith
  have hg : 0 < 4 / (2 - t) - (1 + t) := by
    rw [sub_pos, lt_div_iff₀ hd]
    nlinarith [sq_nonneg (t - 1 / 2)]
  have hlast := mul_nonneg (cycleHandleBlend_deriv_nonneg t) hg.le
  have hb := cycleHandleBlend_bounds t
  have hv : 0 < 4 / (2 - t) ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hd)
  have hfirst : 0 < (1 - cycleHandleBlend t) + cycleHandleBlend t * (4 / (2 - t) ^ 2) := by
    by_cases hlt : cycleHandleBlend t < 1
    · exact add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg hb.1 hv.le)
    · have heq : cycleHandleBlend t = 1 := le_antisymm hb.2 (not_lt.mp hlt)
      simpa only [heq, sub_self, zero_add, one_mul] using hv
  exact add_pos_of_pos_of_nonneg hfirst hlast

theorem cycleHandleRadius_inner {t : ℝ} (ht : t ≤ 1 / 4) :
    cycleHandleRadius t = 1 + t := by
  have hc : cycleHandleBlend t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  simp only [cycleHandleRadius, hc, sub_zero, one_mul, zero_mul, add_zero]

theorem cycleHandleRadius_outer {t : ℝ} (ht : 3 / 4 ≤ t) :
    cycleHandleRadius t = 4 / (2 - t) := by
  have hc : cycleHandleBlend t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  simp only [cycleHandleRadius, hc, sub_self, zero_mul, one_mul, zero_add]

theorem cycleHandleRadius_strictMono : StrictMonoOn cycleHandleRadius (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · exact cycleHandleRadius_smooth.continuousOn.mono (by
      intro t ht
      change t < 2
      linarith [ht.2])
  · intro t ht
    apply cycleHandleRadius_deriv_pos
    have ht1 := interior_subset ht
    linarith [ht1.2]

theorem cycleHandleRadius_inverse {r : ℝ} (hr : r ∈ Icc 1 4) :
    ∃! t : Icc (0 : ℝ) 1, cycleHandleRadius t = r := by
  have h0 : cycleHandleRadius 0 = 1 := by
    rw [cycleHandleRadius_inner (by norm_num)]
    norm_num
  have h1 : cycleHandleRadius 1 = 4 := by
    rw [cycleHandleRadius_outer (by norm_num)]
    norm_num
  have hi := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (cycleHandleRadius_smooth.continuousOn.mono (by
      intro t ht
      change t < 2
      linarith [ht.2]))
  have hr' : r ∈ Icc (cycleHandleRadius 0) (cycleHandleRadius 1) := by
    simpa [h0, h1] using hr
  obtain ⟨t, ht, he⟩ := hi hr'
  refine ⟨⟨t, ht⟩, he, ?_⟩
  intro s hs
  exact Subtype.ext (cycleHandleRadius_strictMono.injOn s.property ht (hs.trans he.symm))

end GC.GraphManifold.Assembly
