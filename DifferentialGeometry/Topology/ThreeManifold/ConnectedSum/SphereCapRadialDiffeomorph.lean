import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapProfileSmooth
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology InnerProductSpace
open Function
namespace DifferentialGeometry.Topology.SphereUnitFilling

lemma hasFDerivAt_norm {x : E3} (hx : x ≠ 0) :
    HasFDerivAt (fun v : E3 => ‖v‖) ((‖x‖)⁻¹ • innerSL ℝ x) x := by
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have hcoe : ((2 : ℕ) • innerSL ℝ x : E3 →L[ℝ] ℝ) = (2 : ℝ) • innerSL ℝ x := by
    rw [two_nsmul, two_smul]
  have hs : HasFDerivAt (fun v : E3 => ‖v‖ ^ 2) ((2 : ℝ) • innerSL ℝ x) x := by
    rw [← hcoe]
    exact (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖x‖ ^ 2))) (‖x‖ ^ 2) :=
    Real.hasDerivAt_sqrt (ne_of_gt hpos)
  have h := hsqrt.comp_hasFDerivAt x hs
  have hval : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := Real.sqrt_sq (norm_nonneg x)
  rw [hval] at h
  have hder : (1 / (2 * ‖x‖)) • ((2 : ℝ) • (innerSL ℝ x)) = (‖x‖)⁻¹ • innerSL ℝ x := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [hder] at h
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h

lemma hasFDerivAt_smul_norm {h : ℝ → ℝ} {h' : ℝ} {x : E3} (hx : x ≠ 0)
    (hh : HasDerivAt h h' ‖x‖) :
    HasFDerivAt (fun v : E3 => h ‖v‖ • v)
      (h ‖x‖ • (1 : E3 →L[ℝ] E3)
        + (h' * (‖x‖)⁻¹) • ((innerSL ℝ x).smulRight x)) x := by
  have hcomp : HasFDerivAt (fun v : E3 => h ‖v‖)
      ((h' * (‖x‖)⁻¹) • innerSL ℝ x) x := by
    have h1 := hh.comp_hasFDerivAt x (hasFDerivAt_norm hx)
    rw [smul_smul] at h1
    exact h1
  have hid : HasFDerivAt (fun v : E3 => v) (1 : E3 →L[ℝ] E3) x := hasFDerivAt_id x
  have h := hcomp.smul hid
  have hsr : (((h' * (‖x‖)⁻¹) • innerSL ℝ x).smulRight x : E3 →L[ℝ] E3)
      = (h' * (‖x‖)⁻¹) • ((innerSL ℝ x).smulRight x) := by
    ext v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply]
    rw [smul_eq_mul, smul_smul]
  rw [hsr] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  rfl

lemma injective_radialCLM {x : E3} (hx : x ≠ 0) {h h' : ℝ} (h0 : h ≠ 0)
    (h1 : h + ‖x‖ * h' ≠ 0) :
    Injective (h • (1 : E3 →L[ℝ] E3) + (h' * (‖x‖)⁻¹) • ((innerSL ℝ x).smulRight x)) := by
  intro v w hvw
  let D : E3 →L[ℝ] E3 := h • (1 : E3 →L[ℝ] E3) + (h' * (‖x‖)⁻¹) • ((innerSL ℝ x).smulRight x)
  have hDval : ∀ u : E3, D u = h • u + (h' * (‖x‖)⁻¹) • (⟪x, u⟫_ℝ • x) := by
    intro u
    simp only [D, add_apply, smul_apply, one_apply_eq_self,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  have hD : D (v - w) = 0 := by
    change D v = D w at hvw
    rw [map_sub, hvw, sub_self]
  have hinner : ⟪x, D (v - w)⟫_ℝ = 0 := by rw [hD, inner_zero_right]
  have hxx : ⟪x, x⟫_ℝ = (‖x‖ : ℝ) ^ 2 := inner_self_eq_norm_sq_to_K x
  rw [hDval, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right, hxx] at hinner
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hkey : ⟪x, v - w⟫_ℝ * (h + ‖x‖ * h') = 0 := by
    have halg : h * ⟪x, v - w⟫_ℝ + h' * (‖x‖)⁻¹ * (⟪x, v - w⟫_ℝ * (‖x‖ : ℝ) ^ 2)
        = ⟪x, v - w⟫_ℝ * (h + ‖x‖ * h') := by
      field_simp
    rw [halg] at hinner
    exact hinner
  have hp : ⟪x, v - w⟫_ℝ = 0 := by
    rcases mul_eq_zero.mp hkey with hh | hh
    · exact hh
    · exact absurd hh h1
  have hzero : h • (v - w) = 0 := by
    have hh := hD
    rw [hDval] at hh
    simp only [hp, smul_zero, zero_smul, add_zero] at hh
    exact hh
  have hsub : v - w = 0 := by
    rcases smul_eq_zero.mp hzero with hh | hh
    · exact absurd hh h0
    · exact hh
  exact sub_eq_zero.mp hsub

def capRadialScaleFun (s : ℝ) : ℝ := -capRadius (2 / s) / s

lemma capRadialMap_eq_smul (v : E3) : capRadialMap v = capRadialScaleFun ‖v‖ • v := by
  rw [capRadialMap, capRadialScale, capRadialScaleFun]
  congr 1
  ring

lemma capRadialScaleFun_ne_zero {s : ℝ} (hs : 0 < s) : capRadialScaleFun s ≠ 0 := by
  have h1 : capRadius (2 / s) ≠ 0 := ne_of_gt (capRadius_pos _)
  have h2 : s ≠ 0 := ne_of_gt hs
  exact div_ne_zero (neg_ne_zero.mpr h1) h2

lemma hasDerivAt_two_div {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun t : ℝ => 2 / t) (-2 / s ^ 2) s := by
  have h := (hasDerivAt_const (x := s) (c := (2 : ℝ))).div (hasDerivAt_id s) hs
  simp only [id_eq] at h
  have hder : (0 * s - 2 * 1) / s ^ 2 = -2 / s ^ 2 := by ring
  rw [hder] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  rfl

lemma hasDerivAt_capRadius_two_div {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => capRadius (2 / t))
      (deriv capRadius (2 / s) * (-2 / s ^ 2)) s := by
  have h2s : (0 : ℝ) < 2 / s := by positivity
  have h := (hasDerivAt_capRadius h2s).comp s (hasDerivAt_two_div (ne_of_gt hs))
  have hfix : -(capDensity (2 / s) * capRadius (2 / s)) = deriv capRadius (2 / s) :=
    (deriv_capRadius h2s).symm
  rw [hfix] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  rfl

lemma hasDerivAt_capRadialScaleFun {s : ℝ} (hs : 0 < s) :
    HasDerivAt capRadialScaleFun (deriv capRadialScaleFun s) s := by
  have h2 : HasDerivAt (fun t : ℝ => capRadius (2 / t))
      (deriv capRadius (2 / s) * (-2 / s ^ 2)) s := hasDerivAt_capRadius_two_div hs
  have h3 : HasDerivAt (fun t : ℝ => -capRadius (2 / t) / t)
      (-((deriv capRadius (2 / s) * (-2 / s ^ 2)) * s - capRadius (2 / s) * 1) / s ^ 2) s := by
    have h := h2.neg.div (hasDerivAt_id s) (ne_of_gt hs)
    simp only [id_eq, Pi.neg_apply] at h
    have hder : ((-(deriv capRadius (2 / s) * (-2 / s ^ 2)) * s - -capRadius (2 / s) * 1) / s ^ 2)
        = -((deriv capRadius (2 / s) * (-2 / s ^ 2)) * s - capRadius (2 / s) * 1) / s ^ 2 := by
      ring
    rw [hder] at h
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    rfl
  have hfun : capRadialScaleFun = fun t : ℝ => -capRadius (2 / t) / t := rfl
  rw [hfun]
  exact h3.congr_deriv h3.deriv.symm

lemma mul_deriv_capRadialScaleFun_add {s : ℝ} (hs : 0 < s) :
    capRadialScaleFun s + s * deriv capRadialScaleFun s
      = -deriv (fun t : ℝ => capRadius (2 / t)) s := by
  have h1 : HasDerivAt (fun t : ℝ => capRadius (2 / t))
      (deriv capRadius (2 / s) * (-2 / s ^ 2)) s := hasDerivAt_capRadius_two_div hs
  have hprod : deriv (fun t : ℝ => t * capRadialScaleFun t) s
      = 1 * capRadialScaleFun s + s * deriv capRadialScaleFun s := by
    have h := deriv_mul (differentiableAt_id) (hasDerivAt_capRadialScaleFun hs).differentiableAt
    have hfun : (id * capRadialScaleFun) = fun t : ℝ => t * capRadialScaleFun t := rfl
    rw [hfun, deriv_id, id_eq] at h
    exact h
  have hev : (fun t : ℝ => t * capRadialScaleFun t) =ᶠ[𝓝 s]
      fun t : ℝ => -capRadius (2 / t) := by
    filter_upwards [isOpen_ne.mem_nhds (ne_of_gt hs)] with t ht
    rw [capRadialScaleFun, neg_div, mul_neg, mul_div_cancel₀ _ ht]
  have hnegderiv : deriv (fun t : ℝ => -capRadius (2 / t)) s
      = -(deriv capRadius (2 / s) * (-2 / s ^ 2)) := by
    have h := h1.neg
    have hfun : (fun t : ℝ => -capRadius (2 / t)) = -(fun t : ℝ => capRadius (2 / t)) := rfl
    rw [hfun]
    exact h.deriv
  rw [hev.deriv_eq, hnegderiv] at hprod
  rw [one_mul] at hprod
  rw [← hprod, h1.deriv]

lemma mul_deriv_capRadialScaleFun_add_ne_zero {s : ℝ} (hs : 0 < s) :
    capRadialScaleFun s + s * deriv capRadialScaleFun s ≠ 0 := by
  have h2s : (0 : ℝ) < 2 / s := by positivity
  have hneg : deriv capRadius (2 / s) < 0 := deriv_capRadius_neg h2s
  have h := mul_deriv_capRadialScaleFun_add (s := s) hs
  rw [h]
  rw [(hasDerivAt_capRadius_two_div hs).deriv]
  refine neg_ne_zero.mpr (mul_ne_zero (ne_of_lt hneg) ?_)
  exact div_ne_zero (by norm_num) (ne_of_gt (pow_pos hs 2))

lemma hasFDerivAt_capRadialMap {x : E3} (hx : x ≠ 0) :
    HasFDerivAt capRadialMap
      (capRadialScaleFun ‖x‖ • (1 : E3 →L[ℝ] E3)
        + (deriv capRadialScaleFun ‖x‖ * (‖x‖)⁻¹) • ((innerSL ℝ x).smulRight x)) x := by
  have hxs : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have h := hasFDerivAt_smul_norm hx (hasDerivAt_capRadialScaleFun hxs)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
  exact capRadialMap_eq_smul v

theorem isLocalDiffeomorph_capRadialMap :
    IsLocalDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ capRadialMap := by
  refine Manifold.isLocalDiffeomorph_of_injective_mfderiv capRadialMap
    contDiff_capRadialMap.contMDiff ?_ rfl
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · have hev : capRadialMap =ᶠ[𝓝 (0 : E3)] fun v : E3 => -(capRadius 2) • v := by
      filter_upwards [Metric.ball_mem_nhds (0 : E3) (by norm_num : (0 : ℝ) < 8 / 7)]
        with v hv
      rw [Metric.mem_ball, dist_zero_right] at hv
      exact capRadialMap_eqOn_closedBall (le_of_lt hv)
    have hlin : fderiv ℝ capRadialMap 0 = -(capRadius 2) • (1 : E3 →L[ℝ] E3) := by
      rw [Filter.EventuallyEq.fderiv_eq hev]
      exact ((hasFDerivAt_id (x := (0 : E3))).const_smul (-(capRadius 2))).fderiv
    rw [mfderiv_eq_fderiv, hlin]
    intro u v huv
    have hcne : -(capRadius 2) ≠ 0 := neg_ne_zero.mpr (ne_of_gt (capRadius_pos 2))
    exact smul_right_injective (M := E3) hcne huv
  · have hxs : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    rw [mfderiv_eq_fderiv]
    rw [(hasFDerivAt_capRadialMap hx).fderiv]
    exact injective_radialCLM hx (capRadialScaleFun_ne_zero hxs)
      (mul_deriv_capRadialScaleFun_add_ne_zero hxs)

end DifferentialGeometry.Topology.SphereUnitFilling
