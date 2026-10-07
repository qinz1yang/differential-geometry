import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HclosGFirstExitP6M4

/-!
# `hscalU` 的 long-depth 合同形 `HU_P6M5`（S-CH11-HSCALU G1，后缀 `_P6M5`）

R-C11-7 处置 D-3（`out/dispositions-R-C11-7-p6-last-gaps.md`）的诚实记账：P6ANCH4 把 seed-distance
closure 化约为指定 U 端点的深度条件曲率控制；该控制仍为独立 analytic obligation。本文件只把这个
obligation 登记成**显式 Prop**，并证明它与 P6ANCH4 binder `hscalU` 逐字对接——不含任何占位证明，不加任何新公理，
不声称已证明 `HU_P6M5`（它不是 Dist `hscal` 的包装；控制对象 / 尺度 / 时间方向 / 定义域 / 常数依赖
均未与 Dist 核对等价）。

* `ObservedHistory.ExitGuard_P6M5`：P6ANCH4 实际使用的"尚未退出"条件，即 `x` 在时刻 `s` 仍 seed-Good：
  `d_s(O_j, x) ≤ d_σ(O_σ, y) + L/√R`（单个时刻 `s`，**不**假设整窗 `[s, v]` 已满足所证 seed closure）。
* `ObservedHistory.HU_P6M5 … B`：long-depth admission。固定宏观参数 `(Rad, σ₁, σ₂, Dw, Dd)` 之后
  `∃ C_U ≥ 1`（`C_U` 在 `n, j, v, w, x, s` 之前），`∀ᶠ n`，对 near-trace 配置 `(j', v, x₁, tr, w)`、
  `x ∈ B_{g_j(v)}(w, Rad/√q_w)`（`q_w := R_j(v, w) ≥ R_n`）、`s ∈ [v − B/q_w, v] ∩ (a_j, b_j)`、
  `ExitGuard(s, x)`：`∀ z ∈ B_{g_j(s)}(x, (C_U q_w)^{-1/2})`，`R_j(s, z) ≤ C_U q_w`。
* `hscalU_of_HU_P6M5`：`(∀ B, HU_P6M5 … B)` ⇒ `hclosG_of_firstExit_P6M4` 的 `hscalU` binder 逐字。
* `HU_P6M5.mono`：深度单调（`B ≤ B'` 时 `HU B'` ⇒ `HU B`，同一 `C_U`）。
* `HU_P6M5.scalar_le_at_top`：`s = v, z = x` 已含 `R_j(v, x) ≤ C_U q_w`（`ExitGuard` 在 `s = v`
  由 `hwseed` + 三角不等式 + `L → ∞` 自动成立）⇒ `HU_P6M5` 不是比 SLT 明显更轻的小叶子。
* 末尾 `example`：`hclosG_of_firstExit_P6M4` 以 `hscalU_of_HU_P6M5` 的输出为唯一残余。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **ExitGuard（`_P6M5`）**：P6ANCH4 实际使用的"尚未退出"条件——`x` 在时刻 `s`（slab `j'` 的 incoming
flow 度量 `g_{j'}(s)`）仍 seed-Good：`d_s(O_{j'}, x) ≤ d_σ(O_σ, y) + L/√R`。只在单个时刻 `s` 要求。 -/
def ObservedHistory.ExitGuard_P6M5 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (n : ℕ) (j' : Fin (Kh n).eventCount)
    (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
    (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (s : ℝ)
    (x : ((Kh n).stage j'.castSucc).Carrier) : Prop :=
  riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
      ((seedTrace n).point j'.castSucc h1 h2) x ≤
    riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) +
      ENNReal.ofReal (L n / Real.sqrt (R n))

/-- **`HU_P6M5 B`：`hscalU` 的 long-depth admission（D-3，`_P6M5`）**。这是**独立 analytic obligation**，
本文件不证它。`q_w := R_j(v, w)`（`= flow.scalar v w`）；窗口 `s ∈ [v − B/q_w, v] ∩ (a_j, b_j)`
（`a_j = time j'.castSucc`，`s ≤ v < time j'.succ`）；`C_U` 在 `n, j, v, w, x, s` 之前。 -/
def ObservedHistory.HU_P6M5 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (B : ℝ) : Prop :=
  ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
    ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
      v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
    ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
        (Dw / Real.sqrt (R n)),
    ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
      (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
    ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
      riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
          ((seedTrace n).point j'.castSucc h1 h2) w ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
      riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
      R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
      ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
          (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
      ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
        (Kh n).time j'.castSucc < s →
        ObservedHistory.ExitGuard_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L n j' h1 h2 s x →
        ∀ z : ((Kh n).stage j'.castSucc).Carrier,
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
              ENNReal.ofReal
                (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
            ((Kh n).event j').incoming.flow.scalar s z ≤
              C * ((Kh n).event j').incoming.flow.scalar v w

/-- **`hscalU_of_HU_P6M5`**：`(∀ B, HU_P6M5 … B)` ⇒ P6ANCH4 `hclosG_of_firstExit_P6M4` 的
`hscalU` binder 逐字（只是把 `ExitGuard_P6M5` 展开、把 `B` 的量词挪到 `Rad` 之前）。 -/
theorem ObservedHistory.hscalU_of_HU_P6M5 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hU : ∀ B : ℝ, ObservedHistory.HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
          (Kh n).time j'.castSucc < s →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stage j'.castSucc).Carrier,
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                ENNReal.ofReal
                  (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
              ((Kh n).event j').incoming.flow.scalar s z ≤
                C * ((Kh n).event j').incoming.flow.scalar v w :=
  fun Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd => hU B Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd

/-- **深度单调（`_P6M5`）**：`B ≤ B'` 时 `HU_P6M5 … B'` ⇒ `HU_P6M5 … B`（窗口 `[v − B/q_w, v]` 变小，
同一 `C_U`）。需要 `0 < R n`（`q_w ≥ R n > 0`）。 -/
theorem ObservedHistory.HU_P6M5.mono (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    {B B' : ℝ} (hBB : B ≤ B')
    (h : ObservedHistory.HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B') :
    ObservedHistory.HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B := by
  intro Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  obtain ⟨C, hC, hev⟩ := h Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  refine ⟨C, hC, hev.mono ?_⟩
  intro n hn j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx s hs1 hsv hs3
    hg z hz
  have hQ : 0 < ((Kh n).event j').incoming.flow.scalar v w := (hR n).trans_le hRw
  have hle : v - B' / ((Kh n).event j').incoming.flow.scalar v w ≤
      v - B / ((Kh n).event j').incoming.flow.scalar v w :=
    sub_le_sub_left (div_le_div_of_nonneg_right hBB hQ.le) v
  exact hn j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx s
    (hle.trans hs1) hsv hs3 hg z hz

/-- **`s = v, z = x` 已含 `R_j(v, x) ≤ C_U q_w`（`_P6M5`）**：`B ≥ 0` 的 `HU_P6M5 … B` 在顶切片 `s = v`
给出 `∀ x ∈ B_{g_j(v)}(w, Rad/√q_w)`，`R_j(v, x) ≤ C_U q_w`。`ExitGuard(v, x)` 在 `s = v` 自动成立：
`d_v(O, x) ≤ d_v(O, w) + d_v(w, x) ≤ d_σ + (L/2 + Rad)/√R ≤ d_σ + L/√R`（`q_w ≥ R n`，
`L ≥ 2 max Rad 0`，后者由 `L → ∞` 最终成立）。故 `HU_P6M5` **不是**比 SLT 明显更轻的小叶子。 -/
theorem ObservedHistory.HU_P6M5.scalar_le_at_top (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop) {B : ℝ} (hB : 0 ≤ B)
    (h : ObservedHistory.HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B)
    (Rad σ₁ σ₂ : ℝ) (h12 : σ₁ ≤ σ₂) (hσ₂ : σ₂ < 0) (Dw Dd : ℝ) (hDw : 0 < Dw) (hDd : 0 < Dd) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ((Kh n).event j').incoming.flow.scalar v x ≤
            C * ((Kh n).event j').incoming.flow.scalar v w := by
  obtain ⟨C, hC, hev⟩ := h Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, hL.eventually_ge_atTop (2 * max Rad 0)] with n hn hLn
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx
  have hRn := hR n
  have hQ : 0 < ((Kh n).event j').incoming.flow.scalar v w := hRn.trans_le hRw
  have hsqR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr hRn
  have hsq : Real.sqrt (R n) ≤ Real.sqrt (((Kh n).event j').incoming.flow.scalar v w) :=
    Real.sqrt_le_sqrt hRw
  have hRad : Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w) ≤
      L n / 2 / Real.sqrt (R n) :=
    calc Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)
        ≤ max Rad 0 / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w) :=
          div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ max Rad 0 / Real.sqrt (R n) :=
          div_le_div_of_nonneg_left (le_max_right _ _) hsqR hsq
      _ ≤ L n / 2 / Real.sqrt (R n) :=
          div_le_div_of_nonneg_right (by linarith) hsqR.le
  have hL0 : 0 ≤ L n / 2 / Real.sqrt (R n) := by
    have := le_max_right Rad 0
    have : 0 ≤ L n := by linarith
    positivity
  have hguard : ObservedHistory.ExitGuard_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L n j'
      h1 h2 v x := by
    unfold ObservedHistory.ExitGuard_P6M5
    calc riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
          ((seedTrace n).point j'.castSucc h1 h2) x
        ≤ riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w +
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v) w x :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ (riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) :=
          add_le_add hwseed (hx.le.trans (ENNReal.ofReal_le_ofReal hRad))
      _ = riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
          rw [add_assoc, ← ENNReal.ofReal_add hL0 hL0]
          congr 2
          ring
  have hBQ : 0 ≤ B / ((Kh n).event j').incoming.flow.scalar v w := div_nonneg hB hQ.le
  have hCQ : 0 < C * ((Kh n).event j').incoming.flow.scalar v w :=
    mul_pos (lt_of_lt_of_le one_pos hC) hQ
  have hxx : riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v) x x <
      ENNReal.ofReal (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) := by
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (one_div_pos.mpr (Real.sqrt_pos.mpr hCQ))
  exact hn j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx v
    (by linarith) le_rfl hv1 hguard x hxx

/-- **consumer（`_P6M5`）**：`hscalU_of_HU_P6M5` 的输出喂给 `hclosG_of_firstExit_P6M4` 的 `hscalU`——
`hclosG`（`hUVG_of_selection_P6M3` 的 binder）的唯一残余即 `∀ B, HU_P6M5 … B`。 -/
example (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hlate : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n))
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hU : ∀ B : ℝ, ObservedHistory.HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B) :=
  ObservedHistory.hclosG_of_firstExit_P6M4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR r hL
    hsmall hclock hRr hwin hlate ha₀ hpin
    (ObservedHistory.hscalU_of_HU_P6M5 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hU)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
