import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaEndToEndC11Q2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeP6M

/-!
# 区域 κ `hκV`（O-CH11-KAPPA2 续窗 G4，后缀 `_C11Q3`；P6ANCH 设计段障碍 O2）

P6 窗口切片二分（P6ANCH2 G3）在切片 `(v, w)` 处调 SLT 窗口版，其 `hnc` 的中心在区域 `U`（不是种子 trace
点），`Pre841` 的 trace-local κ 不覆盖。本文件：
* **合同形** `RegionalKappa_C11Q3 K j U a t ρ κ`：K 层（`RetainedCoreHistory`）、stage `j.castSucc` 的开时段内、
  时间窗 `[a, t]`、区域 `U`、尺度 `≤ ρ` 的受控球体积下界——与 G3 桥
  `RetainedCoreHistory.tested_noncollapse_eventPrefix_P6M`（`Ch11/P6SliceHistoryBridgeP6M:178`）的 `hK`
  **逐字同形**（型对齐 `example`）；
* **生产** `regionalKappa_of_window_C11Q3`：`LocalKappaWindowAt_P6B F (fun _ => 0) A κ`
  （K 链 + Q3 + S7 的产物，`localKappaWindow_zero_of_window_and_small_C11V`）+ 晚期种子 +
  窗口包含 `[a, t] ⊆ [t₀ − r²/2, t₀]` +
  `ρ < r/100` + `U` 的距离约束（`U` 的点在每个 `τ ∈ [a, t]` 离种子 trace 点 `< A r`，即 P6ANCH 的 `hdistV`）
  ⇒ `RegionalKappa_C11Q3 (F.tower.history n) j U a t ρ κ`；
* consumer：经 G3 桥送到 prefix 历史（SLT `hnc` 的形）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **区域 κ（K 层）**：stage `j.castSucc` 的开时段内、时间窗 `[a, t]`、区域 `U`、尺度 `(0, ρ]` 的每个受控球
`Vol ≥ κ b³`。与 `tested_noncollapse_eventPrefix_P6M` 的 `hK` 逐字同形。 -/
def RegionalKappa_C11Q3 (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    (U : Set (K.stage j.castSucc).Carrier) (a t ρ κ : ℝ) : Prop :=
  ∀ (τ : Icc (0 : ℝ) K.toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
    K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
    ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
    ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
      ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
          (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
          (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)

/-- **区域 κ 由 window 形 κ 生产**：window 形 `LocalKappaWindowAt_P6B F (fun _ => 0) A κ` 给出晚期阈值
`T`；对 `T ≤ t₀` 的种子 `(t₀, p, r)`、trace，若 `[a, t] ⊆ [t₀ − r²/2, t₀]`、`ρ < r/100`，且 `U` 的点在每个
`τ ∈ [a, t]` 离种子 trace 点 `< A r`，则 `RegionalKappa_C11Q3 (F.tower.history n) j U a t ρ κ`。 -/
theorem regionalKappa_of_window_C11Q3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {A κ : ℝ} (hκ : 0 ≤ κ)
    (hW : LocalKappaWindowAt_P6B F (fun _ => 0) A κ) :
    ∃ T : ℝ, 0 < T ∧ ∀ n, let H := (F.tower.history n).toHistory;
    ∀ (t₀ : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t₀).Carrier) (r : ℝ),
      T ≤ (t₀ : ℝ) → 2 * r ^ 2 < (t₀ : ℝ) → hasSmallParabolicCurvature H t₀ p r →
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t₀) t₀) p r →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t₀), (aSeed : ℝ) = (t₀ : ℝ) - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t₀)
        (H.activeStage_mono haT) p,
      ∀ (j : Fin (F.tower.history n).eventCount)
        (U : Set ((F.tower.history n).stage j.castSucc).Carrier) (a t ρ : ℝ),
        (t₀ : ℝ) - r ^ 2 / 2 ≤ a → t ≤ (t₀ : ℝ) → ρ < r / 100 →
        (∀ (τ : Icc (0 : ℝ) H.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          ∀ (hav : aSeed ≤ τ) (hvt : τ ≤ t₀),
          ∀ z ∈ U, ∀ zz : (H.stageAt τ).Carrier, HEq zz z →
            riemannianEDistOf (H.stageMetric (H.activeStage τ) τ)
              (seedTrace.point (H.activeStage τ) (H.activeStage_mono hav)
                (H.activeStage_mono hvt)) zz < ENNReal.ofReal (A * r)) →
        RegionalKappa_C11Q3 (F.tower.history n) j U a t ρ κ := by
  obtain ⟨T, hT, hK⟩ := hW
  refine ⟨T, hT, ?_⟩
  intro n H t₀ p r hTt hr hsmall hvol aSeed haT hclock seedTrace j U a t ρ ha ht hρ hU τ haτ hτt _ _
    z hz zz hzz b hb hbρ hball
  have hr0 : 0 < r := hsmall.1
  have hav : aSeed ≤ τ := by
    change (aSeed : ℝ) ≤ (τ : ℝ)
    rw [hclock]
    nlinarith
  have hvt : τ ≤ t₀ := by
    change (τ : ℝ) ≤ (t₀ : ℝ)
    linarith
  have hx := hU τ haτ hτt hav hvt z hz zz hzz
  have h := hK n t₀ p r hTt hr hsmall hvol aSeed haT hclock seedTrace τ hav hvt (by linarith)
    zz hx b (by simpa using hb.le) (hbρ.trans_lt hρ) hball
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **consumer / 型对齐（G4）**：`RegionalKappa_C11Q3` 原样喂 G3 桥 `tested_noncollapse_eventPrefix_P6M`
（prefix 历史上的 SLT `hnc` 形）。 -/
example (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    (U : Set (K.stage j.castSucc).Carrier) {a t ρ κ : ℝ}
    (h : RegionalKappa_C11Q3 K j U a t ρ κ)
    (hend : (K.prefixAt j.castSucc).time (Fin.last (K.prefixAt j.castSucc).eventCount) =
      (K.prefixAt j.castSucc).horizon) :
    ∀ (T : ℝ) (hT : (K.prefixAt j.castSucc).time (Fin.last (K.prefixAt j.castSucc).eventCount) < T)
      (hTs : T < K.time j.succ), T ≤ t → a ≤ T →
        let B := (K.prefixAt j.castSucc).extendHorizon T (hend ▸ hT.le)
          ((K.toHistory.event j).incoming.closedPrefix T hT hTs) (K.event_initial j)
        let tm : Icc (0 : ℝ) B.horizon :=
          ⟨T, (K.prefixAt j.castSucc).horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
        ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
        ∀ (b : ℝ), 0 < b → b ≤ ρ →
          B.toHistory.isParabolicallyRmControlledBall tm yy b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  yy b) :=
  K.tested_noncollapse_eventPrefix_P6M j U h hend

end GC.LongTime.Ch11
