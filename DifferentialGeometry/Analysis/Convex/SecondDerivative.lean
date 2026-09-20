import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open Set Filter Asymptotics
open scoped Topology

namespace DifferentialGeometry.Analysis.Calculus

private theorem norm_sub_le_of_norm_deriv_right_le_uIcc
    {f g : ℝ → ℝ} {x y C : ℝ}
    (hf : ContinuousOn f (uIcc x y))
    (hderiv : ∀ z ∈ uIcc x y, HasDerivWithinAt f (g z) (Ici z) z)
    (hbound : ∀ z ∈ uIcc x y, ‖g z‖ ≤ C) :
    ‖f y - f x‖ ≤ C * |y - x| := by
  rcases le_total x y with hxy | hyx
  · rw [uIcc_of_le hxy] at hf hderiv hbound
    simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using
      norm_image_sub_le_of_norm_deriv_right_le_segment hf
        (fun z hz => hderiv z ⟨hz.1, hz.2.le⟩)
        (fun z hz => hbound z ⟨hz.1, hz.2.le⟩) y ⟨hxy, le_rfl⟩
  · rw [uIcc_of_ge hyx] at hf hderiv hbound
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment hf
      (fun z hz => hderiv z ⟨hz.1, hz.2.le⟩)
      (fun z hz => hbound z ⟨hz.1, hz.2.le⟩) x ⟨hyx, le_rfl⟩
    rw [norm_sub_rev] at h
    simpa only [abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub] using h

theorem isLittleO_sub_sq_of_hasDeriv_right
    {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ}
    (hf : ContinuousOn f U)
    (hderiv : ∀ y ∈ U, HasDerivWithinAt f (g y) (Ici y) y)
    {x : ℝ} (hx : x ∈ U) (hg : g =o[𝓝 x] fun y => y - x) :
    (fun y => f y - f x) =o[𝓝 x] fun y => (y - x) ^ 2 := by
  apply IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hx) (hg.bound hε))
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hsegment : ∀ z ∈ uIcc x y, z ∈ U ∧ ‖g z‖ ≤ ε * ‖z - x‖ := by
    intro z hz
    apply hball
    have hzdist := Real.dist_left_le_of_mem_uIcc hz
    rw [dist_comm x z, dist_comm x y] at hzdist
    exact hzdist.trans_lt hy
  have hbound : ∀ z ∈ uIcc x y, ‖g z‖ ≤ ε * |y - x| := by
    intro z hz
    refine (hsegment z hz).2.trans (mul_le_mul_of_nonneg_left ?_ hε.le)
    simpa only [Real.norm_eq_abs] using abs_sub_left_of_mem_uIcc hz
  have h := norm_sub_le_of_norm_deriv_right_le_uIcc
    (hf.mono (fun z hz => (hsegment z hz).1))
    (fun z hz => hderiv z (hsegment z hz).1) hbound
  simpa only [Real.norm_eq_abs, abs_pow, pow_two, abs_mul, mul_assoc] using h

theorem isLittleO_sub_quadratic_of_hasDeriv_right
    {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ}
    (hf : ContinuousOn f U)
    (hderiv : ∀ y ∈ U, HasDerivWithinAt f (g y) (Ici y) y)
    {x q : ℝ} (hx : x ∈ U) (hg : HasDerivAt g q x) :
    (fun y => f y - f x - g x * (y - x) - q / 2 * (y - x) ^ 2)
      =o[𝓝 x] fun y => (y - x) ^ 2 := by
  let R : ℝ → ℝ := fun y => f y - f x - g x * (y - x) - q / 2 * (y - x) ^ 2
  have hRc : ContinuousOn R U := by
    dsimp [R]
    exact ((hf.sub continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).sub
        (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2))
  have hRd : ∀ y ∈ U,
      HasDerivWithinAt R (g y - g x - (y - x) * q) (Ici y) y := by
    intro y hy
    dsimp only [R]
    convert! (((hderiv y hy).sub_const (f x)).sub
      (((hasDerivAt_id y).sub_const x).const_mul (g x)).hasDerivWithinAt).sub
        ((((hasDerivAt_id y).sub_const x).pow 2).const_mul (q / 2)).hasDerivWithinAt using 1
    simp only [id_eq]
    ring
  have hgo : (fun y => g y - g x - (y - x) * q) =o[𝓝 x] fun y => y - x := by
    simpa only [smul_eq_mul] using hg.isLittleO
  have h := isLittleO_sub_sq_of_hasDeriv_right hU hRc hRd hx hgo
  simpa only [R, sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using h


theorem tendsto_second_central_difference_of_hasDeriv_right
    {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ}
    (hf : ContinuousOn f U)
    (hderiv : ∀ y ∈ U, HasDerivWithinAt f (g y) (Ici y) y)
    {x q : ℝ} (hx : x ∈ U) (hg : HasDerivAt g q x) :
    Tendsto (fun h => (f (x + h) - 2 * f x + f (x - h)) / h ^ 2)
      (𝓝[≠] 0) (𝓝 q) := by
  let R : ℝ → ℝ := fun y => f y - f x - g x * (y - x) - q / 2 * (y - x) ^ 2
  have hR : R =o[𝓝 x] fun y => (y - x) ^ 2 :=
    isLittleO_sub_quadratic_of_hasDeriv_right hU hf hderiv hx hg
  have hp0 : Tendsto (fun h : ℝ => x + h) (𝓝 0) (𝓝 x) := by
    simpa only [add_zero, id_eq] using! tendsto_const_nhds.add
      (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0))
  have hm0 : Tendsto (fun h : ℝ => x - h) (𝓝 0) (𝓝 x) := by
    simpa only [sub_zero, id_eq] using! tendsto_const_nhds.sub
      (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0))
  have hp : Tendsto (fun h => R (x + h) / h ^ 2) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, add_sub_cancel_left] using
      hR.tendsto_div_nhds_zero.comp hp0
  have hm : Tendsto (fun h => R (x - h) / h ^ 2) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, sub_sub_cancel_left, neg_sq] using
      hR.tendsto_div_nhds_zero.comp hm0
  have hlim : Tendsto (fun h => R (x + h) / h ^ 2 + R (x - h) / h ^ 2 + q)
      (𝓝[≠] 0) (𝓝 q) := by
    simpa only [zero_add] using ((hp.add hm).add_const q).mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  dsimp only [R]
  field_simp
  ring

end DifferentialGeometry.Analysis.Calculus

namespace ConvexOn

variable {U : Set ℝ} {f : ℝ → ℝ}

theorem ae_tendsto_second_central_difference (hf : ConvexOn ℝ U f) (hU : IsOpen U) :
    ∀ᵐ x, x ∈ U →
      Tendsto (fun h => (f (x + h) - 2 * f x + f (x - h)) / h ^ 2)
        (𝓝[≠] 0) (𝓝 (deriv (fun y => derivWithin f (Ioi y) y) x)) := by
  have hmono : MonotoneOn (fun y => derivWithin f (Ioi y) y) U := by
    simpa only [hU.interior_eq] using hf.monotoneOn_rightDeriv
  filter_upwards [hmono.ae_differentiableWithinAt_of_mem] with x hdx
  intro hx
  apply DifferentialGeometry.Analysis.Calculus.tendsto_second_central_difference_of_hasDeriv_right
    hU (hf.continuousOn hU) (fun y hy =>
      (hf.hasDerivWithinAt_rightDeriv_of_mem_interior (by rwa [hU.interior_eq])).Ici_of_Ioi)
    hx
  exact ((hdx hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt

end ConvexOn

namespace ConcaveOn

variable {U : Set ℝ} {f : ℝ → ℝ}

theorem ae_tendsto_second_central_difference (hf : ConcaveOn ℝ U f) (hU : IsOpen U) :
    ∀ᵐ x, x ∈ U →
      Tendsto (fun h => (f (x + h) - 2 * f x + f (x - h)) / h ^ 2)
        (𝓝[≠] 0) (𝓝 (deriv (fun y => derivWithin f (Ioi y) y) x)) := by
  filter_upwards [hf.neg.ae_tendsto_second_central_difference hU] with x hx
  intro hxU
  have hlim := (hx hxU).neg
  simp only [derivWithin.neg, deriv.fun_neg, neg_neg] at hlim
  apply hlim.congr'
  filter_upwards with h
  simp only [Pi.neg_apply]
  ring

end ConcaveOn

theorem MonotoneOn.locallyIntegrableOn_deriv {g : ℝ → ℝ} {U : Set ℝ}
    (hg : MonotoneOn g U) (hU : IsOpen U) :
    MeasureTheory.LocallyIntegrableOn (deriv g) U := by
  intro x hx
  obtain ⟨a, b, hxI, hI, hIU⟩ := exists_Icc_mem_subset_of_mem_nhds (hU.mem_nhds hx)
  have hab : a ≤ b := hxI.1.trans hxI.2
  have hm : MonotoneOn g (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hg.mono hIU
  exact ⟨Icc a b, nhdsWithin_le_nhds hI,
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hm.intervalIntegrable_deriv⟩

theorem ConvexOn.locallyIntegrableOn_deriv_rightDeriv {f : ℝ → ℝ} {U : Set ℝ}
    (hf : ConvexOn ℝ U f) (hU : IsOpen U) :
    MeasureTheory.LocallyIntegrableOn (deriv (fun y => derivWithin f (Ioi y) y)) U := by
  have hmono : MonotoneOn (fun y => derivWithin f (Ioi y) y) U := by
    simpa only [hU.interior_eq] using hf.monotoneOn_rightDeriv
  exact hmono.locallyIntegrableOn_deriv hU

theorem ConcaveOn.locallyIntegrableOn_deriv_rightDeriv {f : ℝ → ℝ} {U : Set ℝ}
    (hf : ConcaveOn ℝ U f) (hU : IsOpen U) :
    MeasureTheory.LocallyIntegrableOn (deriv (fun y => derivWithin f (Ioi y) y)) U := by
  have h := (hf.neg.locallyIntegrableOn_deriv_rightDeriv hU).neg
  change MeasureTheory.LocallyIntegrableOn
    (fun x => -deriv (fun y => derivWithin (-f) (Ioi y) y) x) U at h
  simpa only [derivWithin.neg, deriv.fun_neg, neg_neg] using h

namespace DifferentialGeometry.Analysis.Calculus

theorem ae_tendsto_second_central_difference_of_concave_sub_quadratic
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} {C : ℝ}
    (hf : ConcaveOn ℝ U (fun x => f x - C * x ^ 2 / 2)) :
    ∀ᵐ x, x ∈ U →
      Tendsto (fun h => (f (x + h) - 2 * f x + f (x - h)) / h ^ 2)
        (𝓝[≠] 0)
        (𝓝 (deriv (fun y => derivWithin (fun z => f z - C * z ^ 2 / 2) (Ioi y) y) x + C)) := by
  filter_upwards [hf.ae_tendsto_second_central_difference hU] with x hx
  intro hxU
  apply ((hx hxU).add_const C).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ≠ 0 := hh
  field_simp
  ring

theorem locallyIntegrableOn_second_derivative_of_concave_sub_quadratic
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} {C : ℝ}
    (hf : ConcaveOn ℝ U (fun x => f x - C * x ^ 2 / 2)) :
    MeasureTheory.LocallyIntegrableOn
      (fun x => deriv (fun y => derivWithin (fun z => f z - C * z ^ 2 / 2) (Ioi y) y) x + C) U := by
  exact (hf.locallyIntegrableOn_deriv_rightDeriv hU).add
    (MeasureTheory.locallyIntegrableOn_const C)

end DifferentialGeometry.Analysis.Calculus
