import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaBridgeP6B

/-!
# S-CH11-SMALLVOL G3 的 Lean 验证：window（真实 `nr`）+ `hsmall`（Q3 产出形）⇒ `nr := 0` window

P6B `tracedKappa_of_window_P6B` 消费 `LocalKappaWindowAt_P6B F (fun _ => 0) A κ`，即 `[0, r/100)` 全尺度；
`localKappaWindow_small_scale_P6B` 的 `nr v / 100 < r / 100` 前提说明这段曾被隐含地当作已有。这里把
`nr := 0` 消费点改为两个显式前提：

* `hW : LocalKappaWindowAt_P6B F nr A κ`（真实 `nr`，大尺度 window，由 `hKappaLocal` / K0–K6 线供给）；
* `hsmall`（Q3 产出形，**显式展开**，不命名成 Prop）：同一组量词下 `0 < ρ' < nr v / 100`、
  `ρ' < r / 100`、`ρ'` 处 controlled ⇒ `κ' ρ'³ ≤ ballVolume`。`nr v / 100 ≥ r / 100`（空区间）时
  `hW` 无内容，整个 `(0, r/100)` 由 `hsmall` 供给。

结论 `LocalKappaWindowAt_P6B F (fun _ => 0) A (min κ κ')`，可直接喂 `tracedKappa_of_window_P6B`。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **G3 adapter（窗口拼接）**：真实 `nr` 的 window + 小尺度 `hsmall` ⇒ `nr := 0` 的全尺度 window，
`κ` 取 `min κ κ'`，`T` 取两个 `T` 的最大值。 -/
theorem localKappaWindow_zero_of_window_and_small_C11V {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {nr : ℝ → ℝ} {A κ κ' : ℝ}
    (hW : LocalKappaWindowAt_P6B F nr A κ)
    (hsmall : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < nr v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ') :
    LocalKappaWindowAt_P6B F (fun _ => 0) A (min κ κ') := by
  obtain ⟨T₁, hT₁, hK₁⟩ := hW
  obtain ⟨T₂, hT₂, hK₂⟩ := hsmall
  refine ⟨max T₁ T₂, lt_max_of_lt_left hT₁, ?_⟩
  intro n H t p r hTt hr hcurv hvol aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hρ' hρ'r hball
  have hρpos : 0 < ρ' := hball.1
  have hρ3 : 0 ≤ ρ' ^ 3 := pow_nonneg hρpos.le 3
  rcases le_or_gt (nr v / 100) ρ' with hge | hlt
  · have h := hK₁ n t p r ((le_max_left _ _).trans hTt) hr hcurv hvol aSeed haT hclock
      seedTrace v hav hvt hv x hx ρ' hge hρ'r hball
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _) hρ3)).trans h
  · have h := hK₂ n t p r ((le_max_right _ _).trans hTt) hr hcurv hvol aSeed haT hclock
      seedTrace v hav hvt hv x hx ρ' hρpos hlt hρ'r hball
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_right _ _) hρ3)).trans h

/-- consumer：拼出的 window 直接是 `tracedKappa_of_window_P6B` 的 `hW`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {nr : ℝ → ℝ} {A κ κ' : ℝ} (hW : LocalKappaWindowAt_P6B F nr A κ)
    (hsmall : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < nr v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ') :
    True := by
  have := tracedKappa_of_window_P6B
    (localKappaWindow_zero_of_window_and_small_C11V hW hsmall)
  trivial

end GC.LongTime.Ch11
