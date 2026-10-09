import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LocalKappaP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StageBallVolumeRatio

/-!
# P6 / M5 补：小尺度 κ 的 Bishop–Gromov 一步（O-CH11-P6B G4，后缀 `_P6B`）

`hKappaLocal`（`LocalKappaSupply_P6B` 取 `nr` = neck radius）只给尺度 `≥ ℓ := nr/100` 的 κ，而 M8
（`:213` / `:31` 的 `hnc`）要所有小尺度。P6A 建议的"极限端 Ric ≥ 0 + Bishop–Gromov"不能直接用：
κ-noncollapsing 只对 **controlled** 球要求体积下界，小 controlled 球 `B(x, r)` 不保证大球 `B(x, ℓ)`
也 controlled。于是分两种情形：

* (i) `B(x, ℓ)` 也 controlled：`|Rm| ≤ ℓ⁻²` 于 `B_t(x, ℓ)`，树内 Bishop–Gromov
  `exists_riemannianVolumeMeasure_ball_ge_of_rm_le` 给 `vol B(x, r) ≥ c κ r³`（`r ≤ ℓ`）——**本文件**；
* (ii) `x` 的最大 controlled 半径 `< ℓ`：附近 `|Rm| > ℓ⁻² ≈ 10⁴ nr⁻²`，属 canonical 邻域区，需要
  canonical 邻域自身的体积（witness 的 volume 字段 / astra tuple 的 reserve 分支）——**OPEN**。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **情形 (i)**：`x` 处尺度 `ℓ` 的球 controlled 且有 `κ ℓ³ ≤ vol B(x, ℓ)` ⇒ 对所有 `0 < r ≤ ℓ`，
`c κ r³ ≤ vol B(x, r)`，`c > 0` 普适（不依赖 history、`κ`、`ℓ`）。 -/
theorem volume_ge_small_scale_of_controlled_P6B :
    ∃ c : ℝ, 0 < c ∧ ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
      (x : (H.stageAt t).Carrier) {ℓ κ r : ℝ}, 0 ≤ κ →
      H.isParabolicallyRmControlledBall t x ℓ →
      ENNReal.ofReal (κ * ℓ ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x ℓ →
      0 < r → r ≤ ℓ →
      ENNReal.ofReal (c * κ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) x r := by
  obtain ⟨c, hc, hBG⟩ := exists_riemannianVolumeMeasure_ball_ge_of_rm_le.{u}
  refine ⟨c, hc, ?_⟩
  intro H t x ℓ κ r hκ hball hvol hr hrℓ
  have hℓ : 0 < ℓ := hball.1
  obtain ⟨-, a, hat, -, htr⟩ := hball
  have hRm : ∀ z ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) x ℓ,
      ℓ ^ 4 * normSq0S (H.stageMetric (H.activeStage t) t) z 4
        (metricRm04At (H.stageMetric (H.activeStage t) t) z) ≤ 1 := by
    intro z hz
    obtain ⟨B, hB⟩ := htr z hz
    have h := hB.1 t hat le_rfl
    rw [B.endpoint_eq] at h
    exact h
  have hcmp := hBG (H.stageMetric (H.activeStage t) t) x hr hrℓ hRm
  have hratio : c * κ * r ^ 3 = c * (r / ℓ) ^ 3 * (κ * ℓ ^ 3) := by
    field_simp
  calc ENNReal.ofReal (c * κ * r ^ 3)
      = ENNReal.ofReal (c * (r / ℓ) ^ 3) * ENNReal.ofReal (κ * ℓ ^ 3) := by
        rw [hratio, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (c * (r / ℓ) ^ 3) *
          ballVolume (H.stageMetric (H.activeStage t) t) x ℓ := by gcongr
    _ ≤ ballVolume (H.stageMetric (H.activeStage t) t) x r := hcmp

/-- **window 形的小尺度推广（情形 (i)）**：window 形（尺度下界 `nr v/100`）在 `(v, x)` 处、
若 `B_v(x, nr v/100)` controlled 且 `nr v/100 < r/100`，则所有 `0 < r'' ≤ nr v/100` 都有
`c κ r''³ ≤ vol`（`c` 普适）。与 window 形的上段合起来：只要 `x` 的 controlled 半径够到 `nr v/100`，
`x` 在 `(0, r/100)` 全尺度上 `min(κ, cκ)`-noncollapsed。 -/
theorem localKappaWindow_small_scale_P6B :
    ∃ c : ℝ, 0 < c ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
      {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {A κ : ℝ}, 0 ≤ κ →
      LocalKappaWindowAt_P6B F nr A κ →
      ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t), (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        nr v / 100 < r / 100 →
        H.isParabolicallyRmControlledBall v x (nr v / 100) →
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ nr v / 100 →
          ENNReal.ofReal (c * κ * r'' ^ 3) ≤
            ballVolume (H.stageMetric (H.activeStage v) v) x r'' := by
  obtain ⟨c, hc, hsmall⟩ := volume_ge_small_scale_of_controlled_P6B.{u}
  refine ⟨c, hc, ?_⟩
  intro P g F nr A κ hκ hW
  obtain ⟨T, hT, hK⟩ := hW
  refine ⟨T, hT, ?_⟩
  intro n H t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv x hx hlt hctrl
    r'' hr'' hr''le
  have hℓ := hK n t p r hTt hr hsm hvol aSeed haT hclock seedTrace v hav hvt hv x hx
    (nr v / 100) le_rfl hlt hctrl
  exact hsmall H v x hκ hctrl hℓ hr'' hr''le

end GC.LongTime.Ch11
