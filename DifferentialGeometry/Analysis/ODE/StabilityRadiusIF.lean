import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# IMS05 的一维 kernel：沿共形测地线的稳定性不等式 ⇒ 内蕴半径界（O-IFACE G3）

蓝图 IMS05（`master207A.tex` l.18386–18440）与 IAU01（l.18683–18725）：在共形度量
`ĝ = u² g_Σ` 的极小测地线（`g_Σ` 弧长参数 `s ∈ [0, L]`，`L ≥ r`）上，令 `v = log u`、
`Q = q + λ + |∇v|²`；由 `q ≥ σ/2`、`λ ≥ 0`、`|∇v| ≥ |v′|` 得逐点 `Q ≥ σ/2 + v′²`。固定端点的
第二变分给出对所有 `φ ∈ C¹`、`φ(0) = φ(L) = 0`：`0 ≤ ∫₀ᴸ e^{−v} (φ′² − Q φ²) ds`。

本文件把曲面层之后的全部一维论证做成纯分析 kernel：
* `integrand_le_of_weight_IF`：代换 `φ = e^{v/2} ψ` 后的逐点不等式（配方
  `−¾ (v′ψ − ⅔ψ′)² ≤ 0`）：`e^{−v}(φ′² − Qφ²) ≤ (4/3) ψ′² − (σ/2) ψ²`；
* `integral_sin_sq_mul_IF` / `integral_cos_sq_mul_IF`：`∫₀ᴸ sin²(πs/L) = ∫₀ᴸ cos²(πs/L) = L/2`；
* `mul_sq_le_of_sine_stability_IF`：`0 ≤ ∫₀ᴸ ((4/3)(π/L · cos)² − (σ/2) sin²)` ⇒ `σ L² ≤ 8π²/3`
  （即蓝图的 `4π²/(3L²) ≥ σ/2`）；
* `mul_sq_le_of_weighted_stability_IF`：上面的加权稳定性（对所有测试函数）⇒ `σ L² ≤ 8π²/3`；
* `le_two_pi_sqrt_of_mul_sq_le_IF`：`r ≤ L` ⇒ `r ≤ 2π √(2/(3σ))`（IMS05 的结论）；
* `two_pi_sqrt_two_div_three_half_lt_eight_IF` 与 `lt_eight_of_weighted_stability_half_IF`：
  IMS06 用的数值事实 `4π/√3 < 8`，以及 σ = 1/2 时 `L < 8`（排除半径 8 的内蕴球）。

曲面层的归约（特征函数、共形测地线、第二变分）见
`docs/geometrization/chapter8/design-IFACE-K-transport-20261006.md` §B.3。不引入新结构 / 新 Prop。
-/

set_option autoImplicit false
noncomputable section

open Real Set intervalIntegral

namespace DifferentialGeometry.Analysis

/-- 代换 `φ = e^{v/2} ψ`、`φ′ = e^{v/2}(ψ′ + (v′/2) ψ)` 后的逐点不等式：
`Q ≥ σ/2 + v′²` ⇒ `e^{−v}(φ′² − Q φ²) ≤ (4/3) ψ′² − (σ/2) ψ²`。 -/
theorem integrand_le_of_weight_IF (σ v v' ψ ψ' Q : ℝ) (hQ : σ / 2 + v' ^ 2 ≤ Q) :
    Real.exp (-v) * ((Real.exp (v / 2) * (ψ' + v' / 2 * ψ)) ^ 2 -
        Q * (Real.exp (v / 2) * ψ) ^ 2) ≤ 4 / 3 * ψ' ^ 2 - σ / 2 * ψ ^ 2 := by
  have hE : Real.exp (-v) * Real.exp (v / 2) ^ 2 = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    norm_num
  have hrw : Real.exp (-v) * ((Real.exp (v / 2) * (ψ' + v' / 2 * ψ)) ^ 2 -
      Q * (Real.exp (v / 2) * ψ) ^ 2) =
      (Real.exp (-v) * Real.exp (v / 2) ^ 2) * ((ψ' + v' / 2 * ψ) ^ 2 - Q * ψ ^ 2) := by ring
  rw [hrw, hE, one_mul]
  nlinarith [mul_le_mul_of_nonneg_right hQ (sq_nonneg ψ), sq_nonneg (v' * ψ - 2 / 3 * ψ')]

/-- `∫₀ᴸ sin²(π s / L) ds = L / 2`。 -/
theorem integral_sin_sq_mul_IF {L : ℝ} (hL : 0 < L) :
    ∫ s in (0 : ℝ)..L, Real.sin (π / L * s) ^ 2 = L / 2 := by
  have hc : π / L ≠ 0 := div_ne_zero Real.pi_ne_zero hL.ne'
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hc, integral_sin_sq]
  have hπ : π / L * L = π := div_mul_cancel₀ π hL.ne'
  rw [mul_zero, hπ, Real.sin_pi, Real.sin_zero, smul_eq_mul]
  field_simp
  ring

/-- `∫₀ᴸ cos²(π s / L) ds = L / 2`。 -/
theorem integral_cos_sq_mul_IF {L : ℝ} (hL : 0 < L) :
    ∫ s in (0 : ℝ)..L, Real.cos (π / L * s) ^ 2 = L / 2 := by
  have hc : π / L ≠ 0 := div_ne_zero Real.pi_ne_zero hL.ne'
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) hc, integral_cos_sq]
  have hπ : π / L * L = π := div_mul_cancel₀ π hL.ne'
  rw [mul_zero, hπ, Real.sin_pi, Real.sin_zero, smul_eq_mul]
  field_simp
  ring

/-- 正弦检验函数：`0 ≤ ∫₀ᴸ ((4/3)(π/L · cos(πs/L))² − (σ/2) sin²(πs/L))` ⇒ `σ L² ≤ 8π²/3`
（蓝图：`4π²/(3L²) ≥ σ/2`）。 -/
theorem mul_sq_le_of_sine_stability_IF {σ L : ℝ} (hL : 0 < L)
    (h : 0 ≤ ∫ s in (0 : ℝ)..L,
      (4 / 3 * (π / L * Real.cos (π / L * s)) ^ 2 - σ / 2 * Real.sin (π / L * s) ^ 2)) :
    σ * L ^ 2 ≤ 8 * π ^ 2 / 3 := by
  have hcos : IntervalIntegrable (fun s : ℝ => 4 / 3 * (π / L * Real.cos (π / L * s)) ^ 2)
      MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsin : IntervalIntegrable (fun s : ℝ => σ / 2 * Real.sin (π / L * s) ^ 2)
      MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub hcos hsin] at h
  have h1 : ∫ s in (0 : ℝ)..L, 4 / 3 * (π / L * Real.cos (π / L * s)) ^ 2 =
      4 / 3 * (π / L) ^ 2 * (L / 2) := by
    simp_rw [mul_pow]
    rw [← integral_cos_sq_mul_IF hL, ← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    ring
  have h2 : ∫ s in (0 : ℝ)..L, σ / 2 * Real.sin (π / L * s) ^ 2 = σ / 2 * (L / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_sin_sq_mul_IF hL]
  rw [h1, h2] at h
  have key : 0 ≤ (4 / 3 * (π / L) ^ 2 * (L / 2) - σ / 2 * (L / 2)) * (4 * L) :=
    mul_nonneg h (by positivity)
  have hexp : (4 / 3 * (π / L) ^ 2 * (L / 2) - σ / 2 * (L / 2)) * (4 * L) =
      8 * π ^ 2 / 3 - σ * L ^ 2 := by
    field_simp
    ring
  linarith

/-- 加权一维稳定性（对所有 `C¹` 测试函数 `φ`，`φ 0 = φ L = 0`）+ 逐点 `Q ≥ σ/2 + v′²`
⇒ `σ L² ≤ 8π²/3`。测试函数取 `φ = e^{v/2} sin(πs/L)`。 -/
theorem mul_sq_le_of_weighted_stability_IF {σ L : ℝ} (hL : 0 < L) {v v' Q : ℝ → ℝ}
    (hv : ∀ s, HasDerivAt v (v' s) s) (hv' : Continuous v')
    (hQc : ContinuousOn Q (uIcc 0 L)) (hQ : ∀ s ∈ Icc 0 L, σ / 2 + v' s ^ 2 ≤ Q s)
    (hstab : ∀ φ φ' : ℝ → ℝ, (∀ s, HasDerivAt φ (φ' s) s) → Continuous φ' →
      φ 0 = 0 → φ L = 0 →
      0 ≤ ∫ s in (0 : ℝ)..L, Real.exp (-v s) * (φ' s ^ 2 - Q s * φ s ^ 2)) :
    σ * L ^ 2 ≤ 8 * π ^ 2 / 3 := by
  set c : ℝ := π / L with hc
  let ψ : ℝ → ℝ := fun s => Real.sin (c * s)
  let ψ' : ℝ → ℝ := fun s => c * Real.cos (c * s)
  let φ : ℝ → ℝ := fun s => Real.exp (v s / 2) * ψ s
  let φ' : ℝ → ℝ := fun s => Real.exp (v s / 2) * (ψ' s + v' s / 2 * ψ s)
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun s => (hv s).continuousAt
  have hψ (s : ℝ) : HasDerivAt ψ (ψ' s) s := by
    have h := ((hasDerivAt_id s).const_mul c).sin
    simp only [id, mul_one] at h
    convert h using 1
    simp only [ψ']
    ring
  have hφ (s : ℝ) : HasDerivAt φ (φ' s) s := by
    have he : HasDerivAt (fun s => Real.exp (v s / 2)) (Real.exp (v s / 2) * (v' s / 2)) s :=
      ((hv s).div_const 2).exp
    convert he.mul (hψ s) using 1
    simp only [φ']
    ring
  have hφ'c : Continuous φ' := by
    simp only [φ', ψ', ψ]
    fun_prop
  have hφ0 : φ 0 = 0 := by simp [φ, ψ]
  have hφL : φ L = 0 := by
    have : c * L = π := by rw [hc]; exact div_mul_cancel₀ π hL.ne'
    simp [φ, ψ, this]
  have hs := hstab φ φ' hφ hφ'c hφ0 hφL
  apply mul_sq_le_of_sine_stability_IF hL
  refine hs.trans (intervalIntegral.integral_mono_on hL.le ?_ ?_ fun s hs' => ?_)
  · apply ContinuousOn.intervalIntegrable
    have h1 : ContinuousOn (fun s => Real.exp (-v s)) (uIcc 0 L) := by fun_prop
    have h2 : ContinuousOn (fun s => φ' s ^ 2) (uIcc 0 L) := (hφ'c.pow 2).continuousOn
    have h3 : ContinuousOn (fun s => φ s ^ 2) (uIcc 0 L) := by
      have : Continuous φ := continuous_iff_continuousAt.2 fun s => (hφ s).continuousAt
      exact (this.pow 2).continuousOn
    exact h1.mul (h2.sub (hQc.mul h3))
  · apply Continuous.intervalIntegrable
    fun_prop
  · have h := integrand_le_of_weight_IF σ (v s) (v' s) (ψ s) (ψ' s) (Q s) (hQ s hs')
    simpa only [φ, φ', ψ, ψ', hc] using h

/-- IMS05 的结论形式：`r ≤ L` 且 `σ L² ≤ 8π²/3`（`σ > 0`）⇒ `r ≤ 2π √(2/(3σ))`。 -/
theorem le_two_pi_sqrt_of_mul_sq_le_IF {σ L r : ℝ} (hσ : 0 < σ) (hL : 0 ≤ L) (hrL : r ≤ L)
    (h : σ * L ^ 2 ≤ 8 * π ^ 2 / 3) : r ≤ 2 * π * Real.sqrt (2 / (3 * σ)) := by
  have hR : 0 ≤ 2 * π * Real.sqrt (2 / (3 * σ)) := by positivity
  have hR2 : (2 * π * Real.sqrt (2 / (3 * σ))) ^ 2 = 8 * π ^ 2 / (3 * σ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hL2 : L ^ 2 ≤ (2 * π * Real.sqrt (2 / (3 * σ))) ^ 2 := by
    rw [hR2, le_div_iff₀ (by positivity)]
    linarith
  exact hrL.trans (pow_le_pow_iff_left₀ hL hR two_ne_zero |>.mp hL2)

/-- IMS06 的数值事实：`σ = 1/2` 时 `2π √(2/(3σ)) = 4π/√3 < 8`。 -/
theorem two_pi_sqrt_two_div_three_half_lt_eight_IF :
    2 * π * Real.sqrt (2 / (3 * (1 / 2))) < 8 := by
  have hπ : π < 3.15 := Real.pi_lt_d2
  have hπ0 : 0 < π := Real.pi_pos
  have h43 : (2 : ℝ) / (3 * (1 / 2)) = 4 / 3 := by norm_num
  rw [h43]
  have hs : Real.sqrt (4 / 3) < 4 / π := by
    rw [Real.sqrt_lt' (by positivity), div_pow, lt_div_iff₀ (by positivity)]
    nlinarith
  calc 2 * π * Real.sqrt (4 / 3) < 2 * π * (4 / π) :=
        mul_lt_mul_of_pos_left hs (by positivity)
    _ = 8 := by field_simp; ring

/-- IMS06 的一维矛盾：`σ = 1/2` 的加权稳定性在长度 `L` 的区间上成立 ⇒ `L < 8`
（所以半径 8 的内蕴球不可能落在 `R ≥ 1/2` 的 neck band 里）。 -/
theorem lt_eight_of_weighted_stability_half_IF {L : ℝ} (hL : 0 < L) {v v' Q : ℝ → ℝ}
    (hv : ∀ s, HasDerivAt v (v' s) s) (hv' : Continuous v')
    (hQc : ContinuousOn Q (uIcc 0 L)) (hQ : ∀ s ∈ Icc 0 L, 1 / 2 / 2 + v' s ^ 2 ≤ Q s)
    (hstab : ∀ φ φ' : ℝ → ℝ, (∀ s, HasDerivAt φ (φ' s) s) → Continuous φ' →
      φ 0 = 0 → φ L = 0 →
      0 ≤ ∫ s in (0 : ℝ)..L, Real.exp (-v s) * (φ' s ^ 2 - Q s * φ s ^ 2)) :
    L < 8 :=
  (le_two_pi_sqrt_of_mul_sq_le_IF (σ := 1 / 2) (by norm_num) hL.le le_rfl
    (mul_sq_le_of_weighted_stability_IF hL hv hv' hQc hQ hstab)).trans_lt
    two_pi_sqrt_two_div_three_half_lt_eight_IF

/-- Consumer（非空性 / 最优性）：`σ = 8π²/(3L²)` 时正弦检验积分恰为 `0`，所以
`mul_sq_le_of_sine_stability_IF` 的假设可满足，且其界 `σ L² ≤ 8π²/3` 不能改进。 -/
example {L : ℝ} (hL : 0 < L) :
    0 ≤ ∫ s in (0 : ℝ)..L, (4 / 3 * (π / L * Real.cos (π / L * s)) ^ 2 -
      8 * π ^ 2 / (3 * L ^ 2) / 2 * Real.sin (π / L * s) ^ 2) := by
  have hcos : IntervalIntegrable (fun s : ℝ => 4 / 3 * (π / L * Real.cos (π / L * s)) ^ 2)
      MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsin : IntervalIntegrable
      (fun s : ℝ => 8 * π ^ 2 / (3 * L ^ 2) / 2 * Real.sin (π / L * s) ^ 2)
      MeasureTheory.volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h2 : ∫ s in (0 : ℝ)..L, 8 * π ^ 2 / (3 * L ^ 2) / 2 * Real.sin (π / L * s) ^ 2 =
      8 * π ^ 2 / (3 * L ^ 2) / 2 * (L / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_sin_sq_mul_IF hL]
  rw [intervalIntegral.integral_sub hcos hsin, h2]
  have h1 : ∫ s in (0 : ℝ)..L, 4 / 3 * (π / L * Real.cos (π / L * s)) ^ 2 =
      4 / 3 * (π / L) ^ 2 * (L / 2) := by
    simp_rw [mul_pow]
    rw [← integral_cos_sq_mul_IF hL, ← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    ring
  rw [h1]
  apply le_of_eq
  field_simp
  ring

end DifferentialGeometry.Analysis
