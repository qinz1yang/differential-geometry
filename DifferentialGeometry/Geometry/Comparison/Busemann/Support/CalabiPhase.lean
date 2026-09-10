import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def calabiPhase (v : E) (a : ℝ) (x : E) : ℝ :=
  a * ⟪v, x⟫ - ‖x‖ ^ 2 + ⟪v, x⟫ ^ 2

@[simp] theorem calabiPhase_zero (v : E) (a : ℝ) : calabiPhase v a 0 = 0 := by
  simp [calabiPhase]

theorem calabiPhase_contDiff (v : E) (a : ℝ) : ContDiff ℝ ∞ (calabiPhase v a) := by
  have hlin : ContDiff ℝ ∞ (fun x : E => ⟪v, x⟫) :=
    contDiff_const.inner ℝ contDiff_id
  exact ((contDiff_const.mul hlin).sub (contDiff_id.norm_sq (𝕜 := ℝ))).add (hlin.pow 2)


theorem calabiPhase_fderiv_unit (v : E) (hv : ‖v‖ = 1) (a : ℝ) (x : E) :
    fderiv ℝ (calabiPhase v a) x v = a := by
  have hlin := (innerSL ℝ v).hasFDerivAt (x := x)
  have hderiv := ((hlin.const_mul a).sub
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt).add (hlin.pow 2)
  change HasFDerivAt (fun y => a * ⟪v, y⟫ - ‖y‖ ^ 2 + ⟪v, y⟫ ^ 2) _ x at hderiv
  change fderiv ℝ (fun y => a * ⟪v, y⟫ - ‖y‖ ^ 2 + ⟪v, y⟫ ^ 2) x v = a
  rw [hderiv.fderiv]
  simp only [add_apply, sub_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
    real_inner_self_eq_norm_sq, hv, one_pow]
  rw [real_inner_comm v x]
  ring

theorem exists_calabiPhase_negative_on_sphere
    (v : E) (hv : ‖v‖ = 1) (r : ℝ) (hr : 0 < r)
    {V : Set E} (hV : IsCompact V)
    (hsphere : V ⊆ Metric.sphere (0 : E) r) (hmissing : r • v ∉ V) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ V, calabiPhase v a x < 0 := by
  have hnorm (x : E) (hx : x ∈ V) : ‖x‖ = r := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hsphere hx
  have hheight (x : E) (hx : x ∈ V) : -r ≤ ⟪v, x⟫ ∧ ⟪v, x⟫ ≤ r := by
    have h := abs_real_inner_le_norm v x
    rw [hv, hnorm x hx, one_mul] at h
    exact abs_le.mp h
  have hstrict (x : E) (hx : x ∈ V) : ⟪v, x⟫ < r := by
    refine lt_of_le_of_ne (hheight x hx).2 ?_
    intro heq
    have hsq : ‖x - r • v‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm v x, heq,
        norm_smul, Real.norm_eq_abs, abs_of_pos hr, hv, mul_one, hnorm x hx]
      ring
    have hequal : x = r • v := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
    exact hmissing (hequal ▸ hx)
  by_cases hne : V.Nonempty
  · have hcont : Continuous (fun x : E => ⟪v, x⟫) := continuous_const.inner continuous_id
    obtain ⟨z, hz, hmax⟩ := hV.exists_isMaxOn hne hcont.continuousOn
    let k : ℝ := ⟪v, z⟫
    let a : ℝ := (r - k) / 2
    have ha : 0 < a := div_pos (sub_pos.mpr (hstrict z hz)) (by norm_num)
    refine ⟨a, ha, fun x hx => ?_⟩
    have hxheight := hheight x hx
    have hxmax : ⟪v, x⟫ ≤ k := hmax hx
    have hxnorm := hnorm x hx
    dsimp only [calabiPhase]
    rw [hxnorm]
    by_cases hneg : ⟪v, x⟫ < 0
    · have hmul := mul_neg_of_pos_of_neg ha hneg
      have hsq : ⟪v, x⟫ ^ 2 ≤ r ^ 2 := sq_le_sq' hxheight.1 hxheight.2
      linarith
    · have hnonneg := le_of_not_gt hneg
      have hprod := mul_nonneg (sub_nonneg.mpr hxmax) hr.le
      have hsq := mul_nonneg (sub_nonneg.mpr hxheight.2) hnonneg
      have hsmall := mul_nonneg (sub_nonneg.mpr hxheight.2) ha.le
      have hapos := mul_pos ha hr
      dsimp only [a] at *
      nlinarith
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

end DifferentialGeometry.Geometry.Topology

end
