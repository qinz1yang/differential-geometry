/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem exists_positive_fiber_affine_normalization
    (A : ℂ ≃L[ℝ] ℂ) (hA : ∀ v, (A v).im = v.im) {z w : ℂ} (hw : w.im = z.im) :
    ∃ R : ℂ ≃L[ℝ] ℂ, (∀ v, (R v).im = v.im) ∧
      ∃ a b c : ℝ, 0 < a ∧
        ∀ v, R (A (v - z) + w) = ⟨a * v.re + b * v.im + c, v.im⟩ := by
  let a := (A 1).re
  let b := (A Complex.I).re
  let c := w.re - a * z.re - b * z.im
  have ha : a ≠ 0 := by
    intro ha
    have he : A 1 = 0 := Complex.ext ha (by rw [hA]; rfl)
    exact one_ne_zero (A.injective (he.trans (map_zero A).symm))
  have hreal (v : ℂ) : (A v).re = a * v.re + b * v.im := by
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hv, map_add, map_smul, map_smul]
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    dsimp [a, b]
    ring
  have hform (v : ℂ) : A (v - z) + w = ⟨a * v.re + b * v.im + c, v.im⟩ := by
    apply Complex.ext
    · change (A (v - z) + w).re = a * v.re + b * v.im + c
      rw [Complex.add_re, hreal, Complex.sub_re, Complex.sub_im]
      dsimp [c]
      ring
    · change (A (v - z) + w).im = v.im
      rw [Complex.add_im, hA, Complex.sub_im, hw, sub_add_cancel]
  by_cases hpos : 0 < a
  · exact ⟨ContinuousLinearEquiv.refl ℝ ℂ, fun _ => rfl, a, b, c, hpos, hform⟩
  · let R : ℂ ≃L[ℝ] ℂ :=
      Complex.conjCLE.trans (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv
    have hRi (v : ℂ) : (R v).im = v.im := by
      change (-star v).im = v.im
      simp
    refine ⟨R, hRi, -a, -b, -c, neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hpos) ha), ?_⟩
    intro v
    rw [hform]
    apply Complex.ext
    · change -((a * v.re + b * v.im + c)) = -a * v.re + -b * v.im + -c
      ring
    · exact hRi _

theorem exists_diffeomorph_interpolating_fiber_affine
    {l u a₀ a₁ : ℝ} (hlu : l < u) (ha₀ : 0 < a₀) (ha₁ : 0 < a₁)
    (b₀ b₁ c₀ c₁ : ℝ) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞,
      (∀ z, (D z).2 = z.2) ∧
      (∀ z, z.2 ≤ l → D z = (a₀ * z.1 + b₀ * z.2 + c₀, z.2)) ∧
      (∀ z, u ≤ z.2 → D z = (a₁ * z.1 + b₁ * z.2 + c₁, z.2)) ∧
      ∀ y, StrictMono (fun x : ℝ => (D (x, y)).1) := by
  let θ : ℝ → ℝ := fun y => Real.smoothTransition ((y - l) / (u - l))
  have hθ : ContDiff ℝ ∞ θ :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (u - l))
  have hθ₀ (y : ℝ) : 0 ≤ θ y := Real.smoothTransition.nonneg _
  have hθ₁ (y : ℝ) : θ y ≤ 1 := Real.smoothTransition.le_one _
  let a : ℝ → ℝ := fun y => (1 - θ y) * a₀ + θ y * a₁
  let b : ℝ → ℝ := fun y => (1 - θ y) * b₀ + θ y * b₁
  let c : ℝ → ℝ := fun y => (1 - θ y) * c₀ + θ y * c₁
  have hpos (y : ℝ) : 0 < a y := by
    by_cases hy : θ y = 1
    · simpa only [a, hy, sub_self, zero_mul, one_mul, zero_add] using ha₁
    · have ht : 0 < 1 - θ y := sub_pos.mpr ((hθ₁ y).lt_of_ne hy)
      exact add_pos_of_pos_of_nonneg (mul_pos ht ha₀) (mul_nonneg (hθ₀ y) ha₁.le)
  have ha : ContDiff ℝ ∞ a :=
    ((contDiff_const.sub hθ).mul contDiff_const).add (hθ.mul contDiff_const)
  have hb : ContDiff ℝ ∞ b :=
    ((contDiff_const.sub hθ).mul contDiff_const).add (hθ.mul contDiff_const)
  have hc : ContDiff ℝ ∞ c :=
    ((contDiff_const.sub hθ).mul contDiff_const).add (hθ.mul contDiff_const)
  let D : Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ :=
    { toFun := fun z => (a z.2 * z.1 + b z.2 * z.2 + c z.2, z.2)
      invFun := fun z => ((z.1 - b z.2 * z.2 - c z.2) / a z.2, z.2)
      left_inv := by
        intro z
        apply Prod.ext
        · change (a z.2 * z.1 + b z.2 * z.2 + c z.2 - b z.2 * z.2 - c z.2) / a z.2 = z.1
          field_simp [(hpos z.2).ne']
          ring
        · rfl
      right_inv := by
        intro z
        apply Prod.ext
        · change a z.2 * ((z.1 - b z.2 * z.2 - c z.2) / a z.2) +
            b z.2 * z.2 + c z.2 = z.1
          field_simp [(hpos z.2).ne']
          ring
        · rfl
      contMDiff_toFun :=
        ((((ha.comp contDiff_snd).mul contDiff_fst).add
          ((hb.comp contDiff_snd).mul contDiff_snd)).add
            (hc.comp contDiff_snd)).prodMk contDiff_snd |>.contMDiff
      contMDiff_invFun :=
        (((contDiff_fst.sub ((hb.comp contDiff_snd).mul contDiff_snd)).sub
          (hc.comp contDiff_snd)).div (ha.comp contDiff_snd)
            (fun z => (hpos z.2).ne')).prodMk contDiff_snd |>.contMDiff }
  refine ⟨D, fun _ => rfl, ?_, ?_, ?_⟩
  · intro z hz
    have ht : θ z.2 = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) (sub_pos.mpr hlu).le)
    change (a z.2 * z.1 + b z.2 * z.2 + c z.2, z.2) = _
    simp only [a, b, c, ht, sub_zero, one_mul, zero_mul, add_zero]
  · intro z hz
    have ht : θ z.2 = 1 := Real.smoothTransition.one_of_one_le
      ((one_le_div (sub_pos.mpr hlu)).mpr (sub_le_sub_right hz l))
    change (a z.2 * z.1 + b z.2 * z.2 + c z.2, z.2) = _
    simp only [a, b, c, ht, sub_self, zero_mul, one_mul, zero_add]
  · intro y x z hxz
    change a y * x + b y * y + c y < a y * z + b y * y + c y
    linarith [mul_lt_mul_of_pos_left hxz (hpos y)]

end DifferentialGeometry.Topology.Manifold
