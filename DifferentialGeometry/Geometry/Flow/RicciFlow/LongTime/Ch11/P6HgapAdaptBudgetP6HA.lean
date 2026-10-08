import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapBirthSupplyP6JS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProducersLocP6KT2c

/-!
# J8 `CapBirthBudget_P6J7`（局部阈值 `Qs_loc`）的归约（O-CH11-HGAPADAPT / J8KAPPA G3，`_P6HA`）

KT2c `hOpen8J_loc_of_capBirthBudget_P6KT2c` 的 J8 合取是
`CapBirthBudget_P6J7 Ho thr p recordsK Qs_loc Cb`，`thr n = max (T₀ n) (c n·(σ n − L n/R n))`，
`Qs_loc n = max ((n+1)/c n) (ρ(Tno n)²)⁻¹`。本文件证明它**不需要** (SEP-ρ⁺)′，而是 J7SUPPLY 的参数层合同
`CapBirthSupply_P6JS` 在 `ρt n := ρ(Tno n)` 处的实例：
* `qsLoc_eq_P6HA`：hgap 前提 `R ≤ ρ̃(Tn)⁻² = c·ρ(Tno)⁻²`、`n + 1 < R` ⇒ `Qs_loc n = ρ(Tno)⁻²`；
* `window_quarter_P6HA`：`Tn − 1/2 ≤ σ − L²/R`、`1 ≤ R`、`2c < Tno` ⇒ late record（`τ ≥ thr`）满足
  `Tno ≤ 4τ`（late record 落在 `Tno` 的 4-窗内）；
* `deltaRho_le_window_P6HA`：PARAMCOMPAT `SurgeryParamCompat_P6PC p 4` ⇒ `δ_p(τ)ρ_p(τ) ≤ ρ_p(Tno)`
  （`τ ≤ Tno` 用步比，`τ > Tno` 用 antitone + `δ < 1`）；
* **`capBirthBudget_loc_of_paramCompat_P6HA`**（PROVED 归约；PROVISIONAL[`hpc` PARAMCOMPAT `hstep`、
  `hlate` late δ 相对 `Cb n`、`hlink` record 参数 `ρ_p(Tno) ≤ ρ_q(Tno)`]）。
**不能付 hOpen8BJ 槽本身**：槽是 `∀ p recordsK`，`p.delta / p.neckRadius` 不受前提约束，
`hpc / hlate / hlink` 对任意 `p` 不可供（精确障碍见 DELIVERIES 块：J8-a 量词收窄到 witness 形 / J8-b
`T₀ ≥ lateDeltaThr_P6JS` 选择子约束 / J8-c PARAMCOMPAT）。consumer：hgap 帧数据上的实例
`capBirthBudget_hgapFrame_P6HA`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`Qs_loc = ρ(Tno)⁻²`（`_P6HA`，PROVED，纯实数）**。 -/
theorem qsLoc_eq_P6HA {c R ρT : ℝ} {n : ℕ} (hc : 0 < c) (hρ : 0 < ρT)
    (hRρ : R ≤ c * (ρT ^ 2)⁻¹) (hlt : (n : ℝ) + 1 < R) :
    max (((n : ℝ) + 1) / c) (ρT ^ 2)⁻¹ = (ρT ^ 2)⁻¹ := by
  refine max_eq_right ?_
  rw [div_le_iff₀ hc]
  have h2 : 0 < (ρT ^ 2)⁻¹ := by positivity
  nlinarith

/-- **late record 落在 `Tno` 的 4-窗内（`_P6HA`，PROVED，纯实数）**：`Tno = c·Tn`、`2c < Tno`、
`Tn − 1/2 ≤ σ − L²/R`、`1 ≤ R`、`c·(σ − L/R) ≤ τ` ⇒ `Tno ≤ 4τ`。 -/
theorem window_quarter_P6HA {c Tno Tn σ L R τ : ℝ} (hc : 0 < c) (hTn : Tno = c * Tn)
    (h2c : 2 * c < Tno) (hroom : Tn - 1 ^ 2 / 2 ≤ σ - L ^ 2 / R) (hR1 : 1 ≤ R)
    (hτ : c * (σ - L / R) ≤ τ) : Tno ≤ 4 * τ := by
  have hR0 : 0 < R := by linarith
  have hL : L / R ≤ L ^ 2 / R + 1 := by
    have h1 : L ≤ L ^ 2 + 1 := by nlinarith [sq_nonneg (L - 1 / 2)]
    have h2 : L / R ≤ (L ^ 2 + 1) / R := div_le_div_of_nonneg_right h1 hR0.le
    have h3 : 1 / R ≤ 1 := by rw [div_le_one hR0]; exact hR1
    rw [add_div] at h2
    linarith
  have hσ : Tn - 3 / 2 ≤ σ - L / R := by nlinarith
  have hcσ : c * (Tn - 3 / 2) ≤ c * (σ - L / R) := mul_le_mul_of_nonneg_left hσ hc.le
  nlinarith

/-- **PARAMCOMPAT 4-窗 ⇒ `δρ ≤ ρ(Tno)`（`_P6HA`，PROVED）**。 -/
theorem deltaRho_le_window_P6HA {p : CutoffParameters} (hpc : SurgeryParamCompat_P6PC p 4)
    {τ T : ℝ} (hτ0 : 0 ≤ τ) (hT0 : 0 ≤ T) (hw : T ≤ 4 * τ) :
    p.delta τ * p.neckRadius τ ≤ p.neckRadius T := by
  rcases le_or_gt τ T with h | h
  · exact hpc.2 τ T hτ0 h hw
  · have hδ1 := p.delta_lt_one τ hτ0
    have hρ0 := p.neckRadius_pos τ hτ0
    have hanti := hpc.1 (show T ∈ Ici (0 : ℝ) from hT0) (show τ ∈ Ici (0 : ℝ) from hτ0) h.le
    have : p.delta τ * p.neckRadius τ ≤ p.neckRadius τ := by
      have := mul_le_mul_of_nonneg_right hδ1.le hρ0.le
      linarith
    exact this.trans hanti

/-- **J8 budget 的归约（`_P6HA`，PROVED 归约；PROVISIONAL[`hpc`、`hlate`、`hlink`]）**：
record 参数 `p n` 的 PARAMCOMPAT 4-窗 + late δ（相对 `Cb n`）+ `ρ_p(Tno) ≤ ρ_q(Tno)` + 窗口 `Tno ≤ 4τ` +
`Qs ≤ ρ_q(Tno)⁻²` ⇒ `CapBirthBudget_P6J7`（同一 `recordsK`）。经 `capBirthBudget_of_supply_P6JS`
（`ρt n := ρ_q(Tno n)`）。 -/
theorem capBirthBudget_loc_of_paramCompat_P6HA {Ho : ℕ → RetainedCoreHistory.{u}}
    {thr : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n)}
    {Qs Cb : ℕ → ℝ} {q : CutoffParameters} {Tno : ℕ → ℝ} (hTno0 : ∀ n, 0 ≤ Tno n)
    (hpc : ∀ n, SurgeryParamCompat_P6PC (p n) 4)
    (hlink : ∀ n, (p n).neckRadius (Tno n) ≤ q.neckRadius (Tno n))
    (hwin : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      Tno n ≤ 4 * (Ho n).time i.succ)
    (hlate : ∀ n (i : Fin (Ho n).eventCount), thr n ≤ (Ho n).time i.succ →
      (p n).recenterConstant * (p n).delta ((Ho n).time i.succ) ≤ 1 / 2 ∧
        2 * (p n).delta ((Ho n).time i.succ) ^ 2 ≤ Cb n)
    (hQ : ∀ n, Qs n ≤ (q.neckRadius (Tno n) ^ 2)⁻¹) :
    CapBirthBudget_P6J7 Ho thr p recordsK Qs Cb := by
  refine capBirthBudget_of_supply_P6JS
    (ρt := fun n => q.neckRadius (Tno n)) (fun n => q.neckRadius_pos _ (hTno0 n)) hQ ?_
  intro n i hi
  obtain ⟨hΛ, hCb⟩ := hlate n i hi
  refine ⟨hΛ, hCb, ?_⟩
  have ht : 0 ≤ (Ho n).time i.succ := (Ho n).toHistory.time_nonneg i.succ
  exact (deltaRho_le_window_P6HA (hpc n) ht (hTno0 n) (hwin n i hi)).trans (hlink n)

/-- **hgap 帧实例（`_P6HA`，consumer，PROVED 归约；PROVISIONAL[`hpc`、`hlate`、`hlink`]）**：KT2c
hOpen8BJ 的数据形（`thr n = max (T₀ n) (c n·(σ n − L n/R n))`、`Qs_loc`、`Tno n = c n·Tn n`），
`hRρ'`（= hgap `R ≤ ρ̃(Tn)⁻²` 经 `neckRadius_rescale_inv_sq_P6X`）、`hlt`、`hroom`、`h2r`、`hR1` ⇒
J8 合取 `CapBirthBudget_P6J7`。 -/
theorem capBirthBudget_hgapFrame_P6HA {Ho : ℕ → RetainedCoreHistory.{u}}
    {p : ℕ → CutoffParameters} {T₀ c σ L R Tn Tno Cb : ℕ → ℝ}
    {recordsK : ∀ n (i : Fin (Ho n).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (Ho n).time i.succ →
        GeometricCutoffRecord (Ho n).toHistory i (p n)}
    {q : CutoffParameters} (hc : ∀ n, 0 < c n) (hTno : ∀ n, Tno n = c n * Tn n)
    (hTno0 : ∀ n, 0 ≤ Tno n) (h2c : ∀ n, 2 * c n < Tno n)
    (hroom : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) (hR1 : ∀ n, 1 ≤ R n)
    (hRρ' : ∀ n, R n ≤ c n * (q.neckRadius (Tno n) ^ 2)⁻¹) (hlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hpc : ∀ n, SurgeryParamCompat_P6PC (p n) 4)
    (hlink : ∀ n, (p n).neckRadius (Tno n) ≤ q.neckRadius (Tno n))
    (hlate : ∀ n (i : Fin (Ho n).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (Ho n).time i.succ →
      (p n).recenterConstant * (p n).delta ((Ho n).time i.succ) ≤ 1 / 2 ∧
        2 * (p n).delta ((Ho n).time i.succ) ^ 2 ≤ Cb n) :
    CapBirthBudget_P6J7 Ho (fun n => max (T₀ n) (c n * (σ n - L n / R n))) p recordsK
      (fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹) Cb := by
  refine capBirthBudget_loc_of_paramCompat_P6HA hTno0 hpc hlink ?_ hlate ?_
  · intro n i hi
    exact window_quarter_P6HA (hc n) (hTno n) (h2c n) (hroom n) (hR1 n)
      ((le_max_right _ _).trans hi)
  · intro n
    rw [qsLoc_eq_P6HA (hc n) (q.neckRadius_pos _ (hTno0 n)) (hRρ' n) (hlt n)]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
