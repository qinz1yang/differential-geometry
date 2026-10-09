import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# 平面加权长度 `ℓ_ρ(c) = ∫ ρ(c)‖c′‖` 的变分：逐点（固定 `s`）部分（S-W-GEO G2）

固定 `s`：`p = c(s)`、`x = X(s)`（变分场）、`a = c′(s)`、`b = X′(s)`，变分曲线 `c_ε = c + εX`，被积函数

`wlF ε = ρ(p + ε x) · ‖a + ε b‖`，
`wlG1 ε = Dρ(p + εx)(x) ‖a + εb‖ + ρ(p + εx) ⟪a + εb, b⟫/‖a + εb‖`，
`wlG2 ε = D²ρ(p + εx)(x, x) ‖a + εb‖ + 2 Dρ(p + εx)(x) ⟪a + εb, b⟫/‖a + εb‖
          + ρ(p + εx) (‖b‖² − (⟪a + εb, b⟫/‖a + εb‖)²)/‖a + εb‖`。

本文件证 `HasDerivAt (wlF ·) (wlG1 ε) ε` 与 `HasDerivAt (wlG1 ·) (wlG2 ε) ε`（`ρ` 在 `p + εx` 处 `C²`、
`a + εb ≠ 0`）。`wl*` 是实值函数（不是 Prop / 结构）。
-/

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry

/-- 直线 `t ↦ a + t • b` 的导数。 -/
theorem hasDerivAt_line_GE (a b : ℂ) (ε : ℝ) : HasDerivAt (fun t : ℝ => a + t • b) b ε := by
  have h := ((hasDerivAt_id ε).smul_const b).const_add a
  simpa only [id, one_smul] using h

/-- `t ↦ ‖a + t b‖` 的导数 `⟪a + εb, b⟫/‖a + εb‖`（`a + εb ≠ 0`）。 -/
theorem hasDerivAt_norm_line_GE (a b : ℂ) {ε : ℝ} (h : a + ε • b ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖a + t • b‖) (inner ℝ (a + ε • b) b / ‖a + ε • b‖) ε := by
  have h1 := (hasDerivAt_line_GE a b ε).norm_sq
  have hn : ‖a + ε • b‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 h)
  have h2 := h1.sqrt hn
  have h3 : (fun t : ℝ => √(‖a + t • b‖ ^ 2)) = fun t : ℝ => ‖a + t • b‖ := by
    funext t
    exact Real.sqrt_sq (norm_nonneg _)
  rw [h3] at h2
  refine h2.congr_deriv ?_
  rw [Real.sqrt_sq (norm_nonneg _)]
  have : ‖a + ε • b‖ ≠ 0 := norm_ne_zero_iff.2 h
  field_simp

/-- `t ↦ ⟪a + tb, b⟫/‖a + tb‖` 的导数 `(‖b‖² − (⟪a + εb, b⟫/‖a + εb‖)²)/‖a + εb‖`。 -/
theorem hasDerivAt_ratio_line_GE (a b : ℂ) {ε : ℝ} (h : a + ε • b ≠ 0) :
    HasDerivAt (fun t : ℝ => inner ℝ (a + t • b) b / ‖a + t • b‖)
      ((‖b‖ ^ 2 - (inner ℝ (a + ε • b) b / ‖a + ε • b‖) ^ 2) / ‖a + ε • b‖) ε := by
  have hn := hasDerivAt_norm_line_GE a b h
  have hi : HasDerivAt (fun t : ℝ => inner ℝ (a + t • b) b) (inner ℝ b b) ε := by
    have := (hasDerivAt_line_GE a b ε).inner (𝕜 := ℝ) (hasDerivAt_const ε b)
    simpa using this
  have hne : ‖a + ε • b‖ ≠ 0 := norm_ne_zero_iff.2 h
  refine (hi.div hn hne).congr_deriv ?_
  rw [real_inner_self_eq_norm_sq]
  field_simp

/-- `t ↦ ρ(p + t x)` 的导数 `Dρ(p + εx)(x)`。 -/
theorem hasDerivAt_rho_line_GE {ρ : ℂ → ℝ} {p x : ℂ} {ε : ℝ}
    (h : DifferentiableAt ℝ ρ (p + ε • x)) :
    HasDerivAt (fun t : ℝ => ρ (p + t • x)) (fderiv ℝ ρ (p + ε • x) x) ε :=
  h.hasFDerivAt.comp_hasDerivAt ε (hasDerivAt_line_GE p x ε)

/-- `t ↦ Dρ(p + t x)(x)` 的导数 `D²ρ(p + εx)(x, x)`。 -/
theorem hasDerivAt_drho_line_GE {ρ : ℂ → ℝ} {p x : ℂ} {ε : ℝ}
    (h : DifferentiableAt ℝ (fderiv ℝ ρ) (p + ε • x)) :
    HasDerivAt (fun t : ℝ => fderiv ℝ ρ (p + t • x) x)
      (fderiv ℝ (fderiv ℝ ρ) (p + ε • x) x x) ε := by
  have h1 := h.hasFDerivAt.comp_hasDerivAt ε (hasDerivAt_line_GE p x ε)
  have h2 := h1.clm_apply (hasDerivAt_const ε x)
  simpa using h2

/-- 被积函数 `ρ(p + εx) ‖a + εb‖`。 -/
def wlF (ρ : ℂ → ℝ) (p x a b : ℂ) (ε : ℝ) : ℝ := ρ (p + ε • x) * ‖a + ε • b‖

/-- `wlF` 关于 `ε` 的一阶导数。 -/
def wlG1 (ρ : ℂ → ℝ) (p x a b : ℂ) (ε : ℝ) : ℝ :=
  fderiv ℝ ρ (p + ε • x) x * ‖a + ε • b‖ +
    ρ (p + ε • x) * (inner ℝ (a + ε • b) b / ‖a + ε • b‖)

/-- `wlF` 关于 `ε` 的二阶导数。 -/
def wlG2 (ρ : ℂ → ℝ) (p x a b : ℂ) (ε : ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ ρ) (p + ε • x) x x * ‖a + ε • b‖ +
    2 * fderiv ℝ ρ (p + ε • x) x * (inner ℝ (a + ε • b) b / ‖a + ε • b‖) +
    ρ (p + ε • x) * ((‖b‖ ^ 2 - (inner ℝ (a + ε • b) b / ‖a + ε • b‖) ^ 2) / ‖a + ε • b‖)

theorem hasDerivAt_wlF_GE {ρ : ℂ → ℝ} {p x a b : ℂ} {ε : ℝ}
    (hρ : DifferentiableAt ℝ ρ (p + ε • x)) (h : a + ε • b ≠ 0) :
    HasDerivAt (wlF ρ p x a b) (wlG1 ρ p x a b ε) ε :=
  (hasDerivAt_rho_line_GE hρ).mul (hasDerivAt_norm_line_GE a b h)
    |>.congr_deriv (by simp only [wlG1])

theorem hasDerivAt_wlG1_GE {ρ : ℂ → ℝ} {p x a b : ℂ} {ε : ℝ}
    (hρ : DifferentiableAt ℝ ρ (p + ε • x))
    (hρ' : DifferentiableAt ℝ (fderiv ℝ ρ) (p + ε • x)) (h : a + ε • b ≠ 0) :
    HasDerivAt (wlG1 ρ p x a b) (wlG2 ρ p x a b ε) ε :=
  (((hasDerivAt_drho_line_GE hρ').mul (hasDerivAt_norm_line_GE a b h)).add
    ((hasDerivAt_rho_line_GE hρ).mul (hasDerivAt_ratio_line_GE a b h)))
    |>.congr_deriv (by simp only [wlG2]; ring)

end DifferentialGeometry.Geometry
