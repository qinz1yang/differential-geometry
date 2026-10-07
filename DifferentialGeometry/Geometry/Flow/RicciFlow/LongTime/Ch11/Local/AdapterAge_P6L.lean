import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PinchingP6A

/-!
# AD-age（合同 rev1 §R3，外审 R-C11-1 §Q9 9.1；R-C11-2 D-6）：年龄归一尺度的可证部分（`_P6L`）

P6 反例只给 `Q_n r_n² → ∞`、`t_n Q_n → ∞`（不蕴含 `Q_n → ∞`）。SLT:249_P6L（`Λ ≤ R`、`Λ ≤ R·t`）
须在**全历史抛物重标度**后的 history 上调用（`g' = g/(a₀ + s_n)`，`Q' = (a₀ + s_n)Q_n → ∞`）。
本文件交付该 adapter 中**不依赖 history 重标度对象**的部分：
1. 尺度算术：`t_n Q_n → ∞ ⇒ (a₀ + t_n)Q_n → ∞`；selection 时刻 `s_n ≥ t_n − r_n²/2`、`r_n² ≤ t_n` ⇒
   `(a₀ + s_n)Q_n → ∞`。
2. (D2) 时间余量（R-C11-2 D-6）：point selection（`ST/CanonicalTimeControlPointSelection:55`）已输出
   `T − r²/2 ≤ s − L²/Q`；取 `L_n → ∞`（`exists_selection_margin_scale_P6L` 给出满足 selection 的
   `htime`/`hspace` 的 `L_n = (R0_n r_n²)^{1/4}`）⇒ `Q_n (s_n − (T_n − r_n²/2)) → ∞`。
3. pinching 年龄比：晚期窗口 `t ∈ [s − B/Q, s]` 上 `λ = (a₀ + t)/(a₀ + s) ≥ 1/2`（`(a₀+s)Q ≥ 2B`），
   且 `λ ≥ 1/2` 时 `rescalePinchingFunction λ Φ ≤ 2Φ + 2Φ(0)`，后者 admissible（重标度后同一个
   admissible pinching function，外审 9.1 末句）。
**未交（阻塞，见 state HANDOVER）**：`RetainedCoreHistory` / records / closed slab 的抛物重标度对象与
transport（树内只有 `ObservedHistory.rescale`，无 RetainedCoreHistory / GeometricCutoffRecord 版）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- AD-age (1a)：`t_n Q_n → ∞` ⇒ `(a₀ + t_n) Q_n → ∞`（`a₀ ≥ 0`、`Q_n > 0`）。 -/
theorem tendsto_age_mul_of_tendsto_time_mul_P6L {a₀ : ℝ} (ha₀ : 0 ≤ a₀) {t Q : ℕ → ℝ}
    (hQ : ∀ n, 0 < Q n) (h : Tendsto (fun n => t n * Q n) atTop atTop) :
    Tendsto (fun n => (a₀ + t n) * Q n) atTop atTop :=
  tendsto_atTop_mono (fun n => by nlinarith [hQ n]) h

/-- AD-age (1b)：selection 时刻 `s_n ≥ t_n − r_n²/2` 且 `r_n² ≤ t_n`（故 `s_n ≥ t_n/2`）、
`t_n Q_n → ∞` ⇒ `(a₀ + s_n) Q_n → ∞`（外审 9.1："利用选点时刻 `s_n` 与 `t_n` 可比"）。 -/
theorem tendsto_age_mul_of_selection_P6L {a₀ : ℝ} (ha₀ : 0 ≤ a₀) {t s r Q : ℕ → ℝ}
    (hQ : ∀ n, 0 < Q n) (hs : ∀ n, t n - r n ^ 2 / 2 ≤ s n) (hr : ∀ n, r n ^ 2 ≤ t n)
    (h : Tendsto (fun n => t n * Q n) atTop atTop) :
    Tendsto (fun n => (a₀ + s n) * Q n) atTop atTop := by
  have h2 : Tendsto (fun n => (1 / 2 : ℝ) * (t n * Q n)) atTop atTop :=
    h.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono (fun n => ?_) h2
  have h1 : 0 ≤ a₀ + s n - t n / 2 := by linarith [hs n, hr n]
  nlinarith [mul_nonneg h1 (hQ n).le]

/-- (D2) 时间余量（R-C11-2 D-6）：selection 输出 `T_n − r_n²/2 ≤ s_n − L_n²/Q_n`、`L_n → ∞` ⇒
`Q_n (s_n − (T_n − r_n²/2)) → ∞`。 -/
theorem tendsto_selection_time_margin_P6L {T s r Q L : ℕ → ℝ} (hQ : ∀ n, 0 < Q n)
    (hsel : ∀ n, T n - r n ^ 2 / 2 ≤ s n - L n ^ 2 / Q n) (hL : Tendsto L atTop atTop) :
    Tendsto (fun n => Q n * (s n - (T n - r n ^ 2 / 2))) atTop atTop := by
  have hL2 : Tendsto (fun n => L n ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hL
  refine tendsto_atTop_mono (fun n => ?_) hL2
  have hq := hQ n
  have h : L n ^ 2 / Q n ≤ s n - (T n - r n ^ 2 / 2) := by linarith [hsel n]
  calc L n ^ 2 = Q n * (L n ^ 2 / Q n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hq.le

/-- selection 的 `L` 选取：`X_n = R0_n r_n² → ∞` 时 `L_n = √√X_n → ∞`，且 eventually
`2L²/R0 ≤ r²/2`、`2L/√R0 ≤ r/2`（selection 的 `htime`/`hspace` 前提）。 -/
theorem exists_selection_margin_scale_P6L {R0 r : ℕ → ℝ} (hR0 : ∀ n, 0 < R0 n)
    (hr : ∀ n, 0 < r n) (hX : Tendsto (fun n => R0 n * r n ^ 2) atTop atTop) :
    ∃ L : ℕ → ℝ, Tendsto L atTop atTop ∧ ∀ᶠ n in atTop,
      2 * L n ^ 2 / R0 n ≤ r n ^ 2 / 2 ∧ 2 * L n / Real.sqrt (R0 n) ≤ r n / 2 := by
  refine ⟨fun n => Real.sqrt (Real.sqrt (R0 n * r n ^ 2)),
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hX), ?_⟩
  filter_upwards [hX.eventually_ge_atTop 256] with n hn
  set X := R0 n * r n ^ 2 with hXdef
  have hR := hR0 n
  have hrn := hr n
  have hX0 : 0 ≤ X := by positivity
  have hsX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0
  have hs16 : 16 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have ha0 : 0 ≤ Real.sqrt (Real.sqrt X) := Real.sqrt_nonneg _
  have haa : Real.sqrt (Real.sqrt X) * Real.sqrt (Real.sqrt X) = Real.sqrt X :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have ha4 : 4 ≤ Real.sqrt (Real.sqrt X) := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hsR : 0 < Real.sqrt (R0 n) := Real.sqrt_pos.mpr hR
  have hsXr : Real.sqrt X = Real.sqrt (R0 n) * r n := by
    rw [hXdef, Real.sqrt_mul hR.le, Real.sqrt_sq hrn.le]
  constructor
  · rw [div_le_iff₀ hR]
    have h1 : 2 * Real.sqrt (Real.sqrt X) ^ 2 = 2 * Real.sqrt X := by rw [sq, haa]
    rw [h1]
    nlinarith
  · rw [div_le_iff₀ hsR]
    nlinarith

/-- pinching 年龄比（晚期窗口）：`0 < a₀ + s`、`0 < Q`、`2B ≤ (a₀ + s) Q`、`s − B/Q ≤ t` ⇒
`1/2 ≤ (a₀ + t)/(a₀ + s)`。 -/
theorem half_le_age_ratio_P6L {a₀ s t Q B : ℝ} (has : 0 < a₀ + s) (hQ : 0 < Q)
    (hB : 2 * B ≤ (a₀ + s) * Q) (ht : s - B / Q ≤ t) :
    1 / 2 ≤ (a₀ + t) / (a₀ + s) := by
  rw [le_div_iff₀ has]
  have hBQ : B / Q ≤ (a₀ + s) / 2 := by
    rw [div_le_iff₀ hQ]
    linarith
  linarith

/-- `2Φ + 2Φ(0)` admissible（`Φ` admissible）。 -/
theorem AdmissiblePinchingFunction.two_mul_add_P6L {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) :
    AdmissiblePinchingFunction (fun s => 2 * Phi s + 2 * Phi 0) := by
  have h2 : AdmissiblePinchingFunction (fun s => 2 * Phi s) :=
    { contDiff := ContDiff.mul contDiff_const hPhi.contDiff
      pos := fun s => by have := hPhi.pos s; positivity
      mono := fun a b hab => by
        have := hPhi.mono hab
        dsimp only
        linarith
      quotientAntitoneOn := by
        intro a ha b hb hab
        have h1 := hPhi.quotientAntitoneOn ha hb hab
        dsimp only at h1 ⊢
        rw [mul_div_assoc, mul_div_assoc]
        linarith
      quotientTendsto := by
        have heq : (fun s : ℝ => 2 * Phi s / s) = fun s : ℝ => 2 * (Phi s / s) := by
          funext s
          rw [mul_div_assoc]
        rw [heq]
        simpa using hPhi.quotientTendsto.const_mul 2 }
  exact h2.add_const (by have := hPhi.pos 0; positivity)

/-- 重标度 pinching 比较：`1/2 ≤ λ` ⇒ `rescalePinchingFunction λ Φ u ≤ 2Φ(u) + 2Φ(0)`
（`λ ≥ 1` 用 `AdmissiblePinchingFunction.rescale_le`；`λ ∈ [1/2, 1)` 分 `u ≥ 0` / `u < 0`）。 -/
theorem rescalePinchingFunction_le_of_half_le_P6L {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) {lam : ℝ} (hlam : 1 / 2 ≤ lam) (u : ℝ) :
    rescalePinchingFunction lam Phi u ≤ 2 * Phi u + 2 * Phi 0 := by
  have hp0 := hPhi.pos 0
  have hpu := hPhi.pos u
  rcases le_or_gt 1 lam with h1 | h1
  · have := hPhi.rescale_le h1 u
    linarith
  · have hlam0 : 0 < lam := by linarith
    have hinv : lam⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hlam0 (by norm_num)]
      linarith
    have hpl := hPhi.pos (lam * u)
    have hbound : Phi (lam * u) ≤ Phi u + Phi 0 := by
      rcases le_or_gt 0 u with hu | hu
      · have := hPhi.mono (show lam * u ≤ u by nlinarith)
        linarith
      · have := hPhi.mono (show lam * u ≤ 0 by nlinarith)
        linarith
    change lam⁻¹ * Phi (lam * u) ≤ _
    calc lam⁻¹ * Phi (lam * u) ≤ 2 * Phi (lam * u) :=
          mul_le_mul_of_nonneg_right hinv hpl.le
      _ ≤ 2 * Phi u + 2 * Phi 0 := by linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
