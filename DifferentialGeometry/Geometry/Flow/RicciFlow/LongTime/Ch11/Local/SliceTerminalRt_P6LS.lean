import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

/-!
# `hRt`（`R_n · t_n → ∞`）由窗口余量 `hwin` 推出（S-CH11-P6BND G2，后缀 `_P6LS`）

P6 收口主形（`false_of_selection_eventSlab_Kdata_ctrl_P6M2` / final-slab 版 `_P6S`）里有一个 K 层前提
`hRt : Tendsto (fun n => R(t n, yG n) * t n) atTop atTop`（SLT 窗口版的 `Λ ≤ R·t`）。

**发现**：它不需要沿抛物 rescale 搬运 SLT 的其余前提——
* 抛物 rescale `μ` 下 `R ↦ μ R`、`t ↦ t/μ`，故 `R · t` 在 rescale 下**不变**，rescale transport 路线本来
  就推不出 `hRt`（AD-age 的 `(a₀ + s_n) Q_n → ∞` 只在 `R → ∞` 未知时才有用；本收口里
  `R n > qcan n ≥ n + 1` 已给 `R → ∞`）；
* 收口主形的 selection 窗口余量 `hwin : ∀ T > 0, ∀ᶠ n, aSeed n ≤ σ n − T / R n` 与 `aSeed n ∈ [0, horizon]`
  （`aSeed n ≥ 0`）直接给 `σ n ≥ T / R n`，即 `R n · σ n ≥ T`。

本文件：序列层 `tendsto_mul_time_of_window_P6LS`（纯实数）与 K 层 adapter
`tendsto_scalar_mul_time_of_window_P6LS`（`σ n = t n`、`R n = X n` 的 `Icc` 形，`X` 为任意
标量函数，用于 event slab 的 `incoming.flow.scalar` 与 final slab 的 `(G n).flow.scalar`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **序列层**：`a n ≥ 0`、`R n > 0`、`∀ T > 0, ∀ᶠ n, a n ≤ t n − T / R n` ⇒ `R n * t n → ∞`。 -/
theorem tendsto_mul_time_of_window_P6LS {t R a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 0 < R n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, a n ≤ t n - T / R n) :
    Tendsto (fun n => R n * t n) atTop atTop := by
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [hwin (max b 1) (lt_max_of_lt_right one_pos)] with n hn
  have h1 : max b 1 / R n ≤ t n := by linarith [ha n]
  have h2 : max b 1 ≤ t n * R n := (div_le_iff₀ (hR n)).mp h1
  exact (le_max_left b 1).trans (by rw [mul_comm]; exact h2)

/-- **K 层 adapter**：收口主形的 `Icc` 形 `σ` / `aSeed`、`hσ`、`hRn`、`hRpos`、`hwin` ⇒
`hRt`（`X` 任意，`R n = X n`）。 -/
theorem tendsto_scalar_mul_time_of_window_P6LS {Kh : ℕ → ObservedHistory.{u}}
    {σ aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon} {t R X : ℕ → ℝ}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hRn : ∀ n, R n = X n) (hRpos : ∀ n, 0 < R n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) :
    Tendsto (fun n => X n * t n) atTop atTop := by
  have h := tendsto_mul_time_of_window_P6LS (a := fun n => (aSeed n : ℝ)) (t := t) (R := R)
    (fun n => (aSeed n).2.1) hRpos (fun T hT => by
      filter_upwards [hwin T hT] with n hn
      rwa [hσ n] at hn)
  have e : (fun n => R n * t n) = fun n => X n * t n := funext fun n => by rw [hRn n]
  rwa [e] at h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
