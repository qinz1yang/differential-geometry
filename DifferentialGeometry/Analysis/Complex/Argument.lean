import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

open Set

theorem HasDerivAt.arg_of_mem_slitPlane {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hx : f x ∈ Complex.slitPlane) :
    HasDerivAt (fun t => Complex.arg (f t)) (f' / f x).im x := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hf.clog_real hx)
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using h

namespace Complex

private theorem im_circle_deriv_div_offset (d θ : ℝ) :
    ((circleMap 0 1 θ * I) / (circleMap 0 1 θ - (d : ℂ))).im =
      (1 - d * Real.cos θ) / normSq (circleMap 0 1 θ - (d : ℂ)) := by
  rw [div_im]
  simp only [mul_I_im, mul_I_re, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero,
    circleMap_zero_re, circleMap_zero_im, one_mul]
  rw [← sub_div]
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem norm_sq_circle_offset (d θ : ℝ) :
    ‖circleMap 0 1 θ - (d : ℂ)‖ ^ 2 = 1 + d ^ 2 - 2 * d * Real.cos θ := by
  rw [← normSq_eq_norm_sq, normSq_apply]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero,
    circleMap_zero_re, circleMap_zero_im, one_mul]
  nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem slit_circle_offset_of_angle {θ : ℝ}
    (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
    circleMap 0 1 θ - (1 / 2 : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hs : Real.sin θ = 0
  · have hzero := (Real.sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2).mp hs
    subst θ
    left
    norm_num [circleMap]
  · right
    simpa [sub_im, circleMap_zero_im] using hs

private theorem hasDerivAt_arg_circleMap_sub_half {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (fun t => arg (circleMap 0 1 t - (1 / 2 : ℂ)))
      ((1 - Real.cos θ / 2) / ‖circleMap 0 1 θ - (1 / 2 : ℂ)‖ ^ 2) θ ∧
      (2 / 9 : ℝ) ≤ (1 - Real.cos θ / 2) /
        ‖circleMap 0 1 θ - (1 / 2 : ℂ)‖ ^ 2 ∧
      (1 - Real.cos θ / 2) / ‖circleMap 0 1 θ - (1 / 2 : ℂ)‖ ^ 2 ≤ 4 := by
  have hθpi : θ ∈ Ioo (-Real.pi) Real.pi := by
    constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  have hslit := slit_circle_offset_of_angle hθpi
  have hd := ((hasDerivAt_circleMap 0 1 θ).sub_const (1 / 2 : ℂ)).arg_of_mem_slitPlane hslit
  have hformula := im_circle_deriv_div_offset (1 / 2) θ
  rw [normSq_eq_norm_sq] at hformula
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at hformula
  rw [show (1 / 2 : ℝ) * Real.cos θ = Real.cos θ / 2 by ring] at hformula
  have hcos0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc hθ
  have hcos1 := Real.cos_le_one θ
  have hden := norm_sq_circle_offset (1 / 2) θ
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at hden
  have hdenpos : 0 < ‖circleMap 0 1 θ - (1 / 2 : ℂ)‖ ^ 2 := by nlinarith
  refine ⟨?_, (le_div_iff₀ hdenpos).mpr ?_, (div_le_iff₀ hdenpos).mpr ?_⟩
  · rw [hformula] at hd
    exact hd
  · nlinarith
  · nlinarith

theorem hasDerivAt_arg_inner_circle {ρ θ : ℝ} (hρ : 0 < ρ)
    (hθ : θ ∈ Icc (-Real.arccos (ρ / 2)) (Real.arccos (ρ / 2))) :
    HasDerivAt (fun t => arg (circleMap (-1) ρ t - ((-1 + ρ / 2 : ℝ) : ℂ)))
      ((1 - Real.cos θ / 2) / ‖circleMap 0 1 θ - (1 / 2 : ℂ)‖ ^ 2) θ ∧
      (2 / 9 : ℝ) ≤ (1 - Real.cos θ / 2) /
        ‖circleMap 0 1 θ - (1 / 2 : ℂ)‖ ^ 2 ∧
      (1 - Real.cos θ / 2) / ‖circleMap 0 1 θ - (1 / 2 : ℂ)‖ ^ 2 ≤ 4 := by
  have ha : Real.arccos (ρ / 2) ≤ Real.pi / 2 :=
    Real.arccos_le_pi_div_two.mpr (by positivity)
  obtain ⟨hd, hlo, hhi⟩ := hasDerivAt_arg_circleMap_sub_half
    (show θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  refine ⟨?_, hlo, hhi⟩
  have heq : (fun t => arg (circleMap (-1) ρ t - ((-1 + ρ / 2 : ℝ) : ℂ))) =
      fun t => arg (circleMap 0 1 t - (1 / 2 : ℂ)) := by
    funext t
    have hpoint : circleMap (-1) ρ t - ((-1 + ρ / 2 : ℝ) : ℂ) =
        (ρ : ℂ) * (circleMap 0 1 t - (1 / 2 : ℂ)) := by
      simp only [circleMap, zero_add, ofReal_one, one_mul, ofReal_add,
        ofReal_neg, ofReal_div, ofReal_ofNat]
      ring
    rw [hpoint, arg_real_mul _ hρ]
  rw [heq]
  exact hd

private theorem slit_center_sub_circle {ρ θ : ℝ} (hρ : 0 < ρ)
    (hθ : θ ∈ Ioo (0 : ℝ) (2 * Real.pi)) :
    (((-1 + ρ / 2 : ℝ) : ℂ) - circleMap 0 1 θ) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hs : Real.sin θ = 0
  · have hshift : θ - Real.pi ∈ Ioo (-Real.pi) Real.pi := by
      constructor <;> linarith [hθ.1, hθ.2]
    have hsin : Real.sin (θ - Real.pi) = 0 := by rw [Real.sin_sub_pi, hs, neg_zero]
    have hzero := (Real.sin_eq_zero_iff_of_lt_of_lt hshift.1 hshift.2).mp hsin
    have hθeq : θ = Real.pi := by linarith
    left
    simp only [sub_re, ofReal_re, circleMap_zero_re, one_mul, hθeq, Real.cos_pi]
    linarith
  · right
    simpa only [sub_im, ofReal_im, circleMap_zero_im, one_mul, zero_sub, neg_ne_zero] using hs

private theorem cos_le_at_lens_endpoint {ρ θ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hθ : θ ∈ Icc (2 * Real.arccos (ρ / 2))
      (2 * Real.pi - 2 * Real.arccos (ρ / 2))) :
    Real.cos θ ≤ ρ ^ 2 / 2 - 1 := by
  let a := Real.arccos (ρ / 2)
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  have hapi : a ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by positivity)
  have hcos : Real.cos (2 * a) = ρ ^ 2 / 2 - 1 := by
    rw [Real.cos_two_mul, Real.cos_arccos (by linarith : -1 ≤ ρ / 2)
      (by linarith : ρ / 2 ≤ 1)]
    ring
  by_cases hθpi : θ ≤ Real.pi
  · exact (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ 2 * a)
      hθpi hθ.1).trans_eq hcos
  · have href := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ 2 * a)
      (show 2 * Real.pi - θ ≤ Real.pi by linarith) (show 2 * a ≤ 2 * Real.pi - θ by
        linarith [hθ.2])
    rwa [Real.cos_two_pi_sub, hcos] at href

theorem hasDerivAt_arg_outer_circle {ρ θ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hθ : θ ∈ Icc (2 * Real.arccos (ρ / 2))
      (2 * Real.pi - 2 * Real.arccos (ρ / 2))) :
    HasDerivAt (fun t => Real.pi + arg (((-1 + ρ / 2 : ℝ) : ℂ) - circleMap 0 1 t))
      ((1 - (-1 + ρ / 2) * Real.cos θ) /
        ‖circleMap 0 1 θ - ((-1 + ρ / 2 : ℝ) : ℂ)‖ ^ 2) θ ∧
      2 / (9 * ρ) ≤ (1 - (-1 + ρ / 2) * Real.cos θ) /
        ‖circleMap 0 1 θ - ((-1 + ρ / 2 : ℝ) : ℂ)‖ ^ 2 ∧
      (1 - (-1 + ρ / 2) * Real.cos θ) /
        ‖circleMap 0 1 θ - ((-1 + ρ / 2 : ℝ) : ℂ)‖ ^ 2 ≤ 4 / ρ := by
  let c := -1 + ρ / 2
  let z := circleMap 0 1 θ
  have ha0 : 0 < Real.arccos (ρ / 2) := Real.arccos_pos.mpr (by linarith)
  have hθpi : θ ∈ Ioo (0 : ℝ) (2 * Real.pi) := by
    constructor <;> linarith [hθ.1, hθ.2]
  have hslit := slit_center_sub_circle hρ hθpi
  have hd := ((hasDerivAt_circleMap 0 1 θ).const_sub (c : ℂ)).arg_of_mem_slitPlane hslit
  have hratio : (-(z * I)) / ((c : ℂ) - z) = (z * I) / (z - (c : ℂ)) := by
    rw [← neg_sub z (c : ℂ), neg_div_neg_eq]
  have hformula := im_circle_deriv_div_offset c θ
  rw [normSq_eq_norm_sq] at hformula
  have hcos := cos_le_at_lens_endpoint hρ hρ1 hθ
  have hcoslow := Real.neg_one_le_cos θ
  have hcneg : c ≤ 0 := by dsimp only [c]; linarith
  have hnumlow : ρ / 2 ≤ 1 - c * Real.cos θ := by
    have hm := mul_le_mul_of_nonpos_left hcoslow hcneg
    dsimp only [c] at hm ⊢
    nlinarith
  have hnumhigh : 1 - c * Real.cos θ ≤ ρ := by
    have hm := mul_le_mul_of_nonpos_left hcos hcneg
    have hρsq : ρ ^ 2 ≤ ρ := by nlinarith
    have hρcube : 0 ≤ ρ ^ 3 := by positivity
    dsimp only [c] at hm ⊢
    nlinarith
  have hden := norm_sq_circle_offset c θ
  have hdenlow : ρ ^ 2 / 4 ≤ ‖z - (c : ℂ)‖ ^ 2 := by
    have hm := mul_le_mul_of_nonpos_left hcoslow hcneg
    change ‖z - (c : ℂ)‖ ^ 2 = _ at hden
    dsimp only [c] at hm hden
    nlinarith
  have hdenhigh : ‖z - (c : ℂ)‖ ^ 2 ≤ 9 * ρ ^ 2 / 4 := by
    have hm := mul_le_mul_of_nonpos_left hcos hcneg
    have hρcube : 0 ≤ ρ ^ 3 := by positivity
    change ‖z - (c : ℂ)‖ ^ 2 = _ at hden
    dsimp only [c] at hm hden
    nlinarith
  have hdenpos : 0 < ‖z - (c : ℂ)‖ ^ 2 := lt_of_lt_of_le (by positivity) hdenlow
  refine ⟨?_, ?_, ?_⟩
  · have hd' := hd.const_add Real.pi
    change HasDerivAt (fun t => Real.pi + arg ((c : ℂ) - circleMap 0 1 t))
      ((-(z * I)) / ((c : ℂ) - z)).im θ at hd'
    rw [hratio] at hd'
    change HasDerivAt (fun t => Real.pi + arg ((c : ℂ) - circleMap 0 1 t))
      ((circleMap 0 1 θ * I) / (circleMap 0 1 θ - (c : ℂ))).im θ at hd'
    rw [hformula] at hd'
    exact hd'
  · apply (le_div_iff₀ hdenpos).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 9 * ρ)).mpr
    change 2 * ‖z - (c : ℂ)‖ ^ 2 ≤ (1 - c * Real.cos θ) * (9 * ρ)
    have hm := mul_le_mul_of_nonneg_right hnumlow (by positivity : 0 ≤ 9 * ρ)
    nlinarith
  · apply (div_le_iff₀ hdenpos).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hρ).mpr
    nlinarith

end Complex

end
