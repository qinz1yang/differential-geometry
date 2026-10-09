import DifferentialGeometry.Geometry.Curvature.IndexFormAlgebraGE
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Basic

/-!
# 指标形式：逐点的复数 / 分量翻译（S-W-GEO G2）

`a = c′(s)`、`b = c″(s)`、`ν = ‖a‖⁻¹ • (I a)`（单位法向）、`ν′ = ‖a‖⁻¹ • (I b) −
(⟪a, b⟫/‖a‖³) • (I a)`；`L1 = Dρ(c)`、`L2 = D²ρ(c)`；变分场 `X = f ν`（`X′ = f₁ ν + f ν′`）与 `Y ν`。
`index_pointwise_GE`：指标形式被积函数 `= d2 + zp − d1`（`WeightedLengthVariationGE` 的被积函数形状），
由 `IndexFormAlgebraGE.index_identity_GE`（纯实数）与复数分量展开得到。
-/

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry

/-- `ℂ` 上的实线性映射按两个坐标分量展开。 -/
theorem clm_complex_apply_GE {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℂ →L[ℝ] F) (w : ℂ) : L w = w.re • L 1 + w.im • L Complex.I := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul]

theorem inner_complex_GE (a b : ℂ) : inner ℝ a b = a.re * b.re + a.im * b.im := by
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem sq_norm_complex_GE (a : ℂ) : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- 单位法向 `ν = ‖a‖⁻¹ • (I a)`。 -/
def nuVec (a : ℂ) : ℂ := ‖a‖⁻¹ • (Complex.I * a)

/-- `ν` 沿曲线的导数（`a′ = b`）：`‖a‖⁻¹ • (I b) − (⟪a, b⟫/‖a‖³) • (I a)`。 -/
def nuDeriv (a b : ℂ) : ℂ :=
  ‖a‖⁻¹ • (Complex.I * b) + (-(inner ℝ a b / ‖a‖) / ‖a‖ ^ 2) • (Complex.I * a)

theorem clm1_expand_GE (L : ℂ →L[ℝ] ℝ) (w : ℂ) : L w = w.re * L 1 + w.im * L Complex.I := by
  rw [clm_complex_apply_GE L w]
  simp

theorem clm2_expand_GE (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (u w : ℂ) :
    L u w = u.re * w.re * L 1 1 + u.re * w.im * L 1 Complex.I +
      u.im * w.re * L Complex.I 1 + u.im * w.im * L Complex.I Complex.I := by
  rw [clm_complex_apply_GE L u]
  simp only [add_apply, smul_apply]
  rw [clm1_expand_GE (L 1) w, clm1_expand_GE (L Complex.I) w]
  simp only [smul_eq_mul]
  ring

theorem nuVec_re_GE (a : ℂ) : (nuVec a).re = -a.im / ‖a‖ := by
  simp only [nuVec, Complex.smul_re, Complex.mul_re, Complex.I_re, Complex.I_im, smul_eq_mul]
  ring

theorem nuVec_im_GE (a : ℂ) : (nuVec a).im = a.re / ‖a‖ := by
  simp only [nuVec, Complex.smul_im, Complex.mul_im, Complex.I_re, Complex.I_im, smul_eq_mul]
  ring

theorem nuDeriv_re_GE (a b : ℂ) :
    (nuDeriv a b).re = -b.im / ‖a‖ + (a.re * b.re + a.im * b.im) / ‖a‖ * a.im / ‖a‖ ^ 2 := by
  simp only [nuDeriv, Complex.add_re, Complex.smul_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    smul_eq_mul, inner_complex_GE]
  ring

theorem nuDeriv_im_GE (a b : ℂ) :
    (nuDeriv a b).im = b.re / ‖a‖ - (a.re * b.re + a.im * b.im) / ‖a‖ * a.re / ‖a‖ ^ 2 := by
  simp only [nuDeriv, Complex.add_im, Complex.smul_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    smul_eq_mul, inner_complex_GE]
  ring

theorem index_pointwise_GE (L1 : ℂ →L[ℝ] ℝ) (L2 : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {R : ℝ} {a b : ℂ}
    (ha : a ≠ 0) (hR : 0 < R) (f f1 Yp : ℝ) :
    (L1 a * f + R * f1) ^ 2 / (R * ‖a‖) -
      (-R⁻¹ ^ 2 * ((L2 1 1 + L2 Complex.I Complex.I) / R -
        (L1 1 ^ 2 + L1 Complex.I ^ 2) / R ^ 2)) * (R * ‖a‖) * (R * f) ^ 2 =
    (L2 (f • nuVec a) (f • nuVec a) * ‖a‖ +
        2 * L1 (f • nuVec a) *
          (inner ℝ a (f1 • nuVec a + f • nuDeriv a b) / ‖a‖) +
        R * ((‖f1 • nuVec a + f • nuDeriv a b‖ ^ 2 -
          (inner ℝ a (f1 • nuVec a + f • nuDeriv a b) / ‖a‖) ^ 2) / ‖a‖)) +
    ((L2 a a + L1 b) * f ^ 2 / ‖a‖ + L1 a * (2 * f * f1) / ‖a‖ -
        L1 a * f ^ 2 * (inner ℝ a b / ‖a‖) / ‖a‖ ^ 2) -
    (L1 ((f ^ 2 * (L1 (nuVec a) / R)) • nuVec a) * ‖a‖ +
        R * (inner ℝ a (Yp • nuVec a + (f ^ 2 * (L1 (nuVec a) / R)) • nuDeriv a b) / ‖a‖)) := by
  have hr : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hr2 : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := sq_norm_complex_GE a
  have hr0 : ‖a‖ ≠ 0 := hr.ne'
  have eL1ν : L1 (nuVec a) = (nuVec a).re * L1 1 + (nuVec a).im * L1 Complex.I :=
    clm1_expand_GE L1 _
  have eL1a : L1 a = a.re * L1 1 + a.im * L1 Complex.I := clm1_expand_GE L1 _
  have eL1b : L1 b = b.re * L1 1 + b.im * L1 Complex.I := clm1_expand_GE L1 _
  have eL2νν := clm2_expand_GE L2 (nuVec a) (nuVec a)
  have eL2aa := clm2_expand_GE L2 a a
  refine index_identity_GE (a1 := a.re) (a2 := a.im) (b1 := b.re) (b2 := b.im) (r := ‖a‖)
    (R := R) (g1 := L1 1) (g2 := L1 Complex.I) (h11 := L2 1 1) (h12 := L2 1 Complex.I)
    (h21 := L2 Complex.I 1) (h22 := L2 Complex.I Complex.I) (f := f) (f1 := f1) (Yp := Yp)
    hr hR hr2 ?_ ?_ ?_ ?_
  · simp only [map_smul, smul_apply, smul_eq_mul, eL1ν, eL2νν, inner_complex_GE,
      sq_norm_complex_GE, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      nuVec_re_GE, nuVec_im_GE, nuDeriv_re_GE, nuDeriv_im_GE]
    field_simp
  · simp only [map_smul, smul_eq_mul, eL1ν, inner_complex_GE,
      Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      nuVec_re_GE, nuVec_im_GE, nuDeriv_re_GE, nuDeriv_im_GE]
    field_simp
  · simp only [eL1a, eL1b, eL2aa, inner_complex_GE]
    field_simp
    ring
  · simp only [eL1a]
    field_simp
    ring

end DifferentialGeometry.Geometry
