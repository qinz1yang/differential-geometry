import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.WindowGlueC11V
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.HsmallAssemblySeedScaleC11V5

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL5 G2：window 拼接的种子尺度变体（`_C11V5`，KAPPA3 G7 精确形 (ii)）

`localKappaWindow_zero_of_window_and_small_C11V` 的变体：真实 `nr` 的 window `hW`
（`LocalKappaWindowAt_P6B F nr A κ`，全种子成立，例如 `localKappaWindow_of_late_P6B` ∘ KAPPA3 G6
`localKappaP6B_of_reducedVolumeScaled_C11Q4`）
+ 小尺度 `hsmall`（G1 `hsmall_of_wide_window_late_seedScale_C11V5` 的结论形，每个 `v` 多 `nr v ≤ r`）
⇒ **`nr := 0` 的 window，只对满足 `∀ w ∈ [t − r²/2, t], nr w ≤ r` 的种子**
（该前提在种子层，位于体积前提之后、`aSeed` 之前；`ρ'` 下界 `nr := 0` 退化为 `0 ≤ ρ'`，
与 `LocalKappaWindowAt_P6B F (fun _ => 0) A κ` 的 `0 / 100 ≤ ρ'` 等价）。
证明：`nr v / 100 ≤ ρ'` 走 `hW`，`ρ' < nr v / 100` 走 `hsmall`（由种子前提给出 `nr v ≤ r`）。
只在 P6 种子路径上消费，不改全称合同。
-/

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **G2（(ii)）**：真实 `nr` 的 window + 种子尺度 `hsmall` ⇒ `nr := 0` window，只对
`∀ w ∈ [t − r²/2, t], nr w ≤ r` 的种子；`κ` 取 `min κ κ'`，`T` 取两个 `T` 的最大值。 -/
theorem localKappaWindow_zero_of_window_and_small_seedScale_C11V5 {P : OrientedThreeStage.{u}}
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
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → nr v ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < nr v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ') :
    ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → nr w ≤ r) →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (min κ κ' * ρ' ^ 3) ≤
            ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨T₁, hT₁, hK₁⟩ := hW
  obtain ⟨T₂, hT₂, hK₂⟩ := hsmall
  refine ⟨max T₁ T₂, lt_max_of_lt_left hT₁, ?_⟩
  intro n H t p r hTt hr hcurv hvol hscale aSeed haT hclock seedTrace v hav hvt hv x hx ρ' hρ'0
    hρ'r hball
  have hρpos : 0 < ρ' := hball.1
  have hρ3 : 0 ≤ ρ' ^ 3 := pow_nonneg hρpos.le 3
  rcases le_or_gt (nr v / 100) ρ' with hge | hlt
  · have h := hK₁ n t p r ((le_max_left _ _).trans hTt) hr hcurv hvol aSeed haT hclock
      seedTrace v hav hvt hv x hx ρ' hge hρ'r hball
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _) hρ3)).trans h
  · have hnrv : nr v ≤ r := hscale v hv hvt
    have h := hK₂ n t p r ((le_max_right _ _).trans hTt) hr hcurv hvol aSeed haT hclock
      seedTrace v hav hvt hv hnrv x hx ρ' hρpos hlt hρ'r hball
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_right _ _) hρ3)).trans h

/-- **consumer（G2）**：KAPPA3 G6 的 `LocalKappaSupply_P6B`（`L = 1`，尺度 K5 给出）+ S7 ⇒ 真实 `nr` 的
window（`localKappaWindow_of_late_P6B`），再拼 G1 形的 `hsmall` ⇒ 种子尺度 window-zero。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr v : ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α) (hK5 : SeedReducedVolumeScaled_C11Q4 F δ α nr v)
    {A : ℝ} (hA : 0 < A) {κ' : ℝ} (hκ' : 0 < κ')
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
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → nr v ≤ r →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < nr v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ') :
    ∃ κ'' : ℝ, 0 < κ'' ∧
    ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → nr w ≤ r) →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
            ballVolume (H.stageMetric (H.activeStage v) v) x ρ' := by
  obtain ⟨κ₁, hκ₁, hW₁⟩ := localKappaWindow_of_late_P6B
    (localKappaLateSupply_of_envelope_P6B hacc
      (localKappaP6B_of_reducedVolumeScaled_C11Q4 hK5)) A hA
  exact ⟨min κ₁ κ', lt_min hκ₁ hκ',
    localKappaWindow_zero_of_window_and_small_seedScale_C11V5 hW₁ hsmall⟩

end GC.LongTime.Ch11
