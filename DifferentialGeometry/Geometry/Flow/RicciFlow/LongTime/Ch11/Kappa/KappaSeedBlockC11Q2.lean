import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaWeightedMinC11Q2

/-!
# K5 的 block 形对接（O-CH11-KAPPA2 G3，后缀 `_C11Q2`）

donor orphan `exists_uniform_regular_endpoint_block_of_half_clock_action`
（`…/Action/UniformRegularEndpointBlock:126`，03:4x 未落地）的结论是 **block 形**：时钟
`v = √3 r/2`（深度 `3r²/4`）切片上 `U = B(O, r/100)`，`vol U ≥ κ₀ v³`（`κ₀ = A⁻¹e⁻⁵⁷/(512·100³)`），
`U` 每点是非 barely admissible 极小端点且 `𝓛 ≤ 2·Dfull·v`；输入是半时钟端点 `qHalf ∈ B(O_half, r/10)`
（作用量 `< factor(A)·r`）——即 K4 的产物。它的 patch 半径 `r/100` **小于** K5a 合同的 `r/20`，所以 URE
**不能**实例化 `SeedPatchLowAction_C11Q`（K5a）；正确的接口是直接产 K5：
* `SeedRegularBlock_C11Q2 F δ α nr C₄ D κ`：URE 结论形的显式前提（输入 = K4 的低作用量点）；
* `seedReducedVolumeLower_of_block_C11Q2`：K4 + block ⇒ `SeedReducedVolumeLower_C11Q`
  （`v_A = κ(A) e^{−D(A)} (4π)^{−3/2}`，用已证的 K5 体积解释 `redVolume_ge_of_lowActionPatch_C11Q`）；
  **K0 / K5a 都不再需要**；
* 链：WeightedMinBound + K3（或 G1 窗口 K3）+ block ⇒ `LocalKappaWideSupply_C11Q`。
URE 落地后的实例化目标形见 state 文件（`D = factor + e^{9/2} + 4`、`κ = κ₀`、`C₄ = weightedMinLengthConst`
在 `C = SingularBarrier.bound(2A + 160·derivBound² + 3/40)` 时 `factor = weightedMinLevel`）。
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

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

/-- **种子 regular-endpoint block**（URE 结论形，显式前提）：在 accuracy 下、每个种子 / trace / 基点
（受控测试球 `ϱ₀ ≥ nr(t)/100`）/ 真实地板 `Bf`，若半时钟切片 `s₁ = t − r²/2` 上 `B(O₁, r/10)` 内有
`l ≤ C₄(A)` 的非 barely admissible 极小端点（K4 的产物），则时钟 `w = √(3/4)·r` 的切片上有开集 `U`，
`vol U ≥ κ(A) w³`，`U` 每点非 barely admissible 极小且 `l ≤ D(A)`。 -/
def SeedRegularBlock_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (δ : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (nr : ℝ → ℝ)
    (C₄ D κ : ℝ → ℝ) : Prop :=
  ∀ A, 0 < A → ∀ n, let R := F.tower.history n; let H := R.toHistory;
  ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
    2 * r ^ 2 < (t : ℝ) → (∀ s ∈ Icc ((t : ℝ) / 2) t, δ s < α A s) →
    hasSmallParabolicCurvature H t p r →
    ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
    ∀ (b : Icc (0 : ℝ) H.horizon) (hbt : b ≤ t), (b : ℝ) = (t : ℝ) - r ^ 2 →
    ∀ seedTrace : BackwardPointTrace H (H.activeStage b) (H.activeStage t)
      (H.activeStage_mono hbt) p,
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
    ∀ ϱ₀ : ℝ, nr t / 100 ≤ ϱ₀ → H.isParabolicallyRmControlledBall t x ϱ₀ →
    ∀ Bf : ℝ, ScalarFloor_C11Q R Bf →
    ∀ (s₁ : Icc (0 : ℝ) H.horizon) (hbs₁ : b ≤ s₁) (hs₁t : s₁ ≤ t),
      (s₁ : ℝ) = (t : ℝ) - r ^ 2 / 2 →
      (∃ q₁ ∈ riemannianBallOf (H.stageMetric (H.activeStage s₁) s₁)
          (seedTrace.point (H.activeStage s₁) (H.activeStage_mono hbs₁)
            (H.activeStage_mono hs₁t)) (r / 10),
        IsLowActionEndpoint_C11Q R Bf t s₁ x (C₄ A) q₁) →
      ∃ U : Set (R.stage (H.activeStage (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)))).Carrier,
        IsOpen U ∧
        ENNReal.ofReal (κ A * (Real.sqrt (3 / 4) * r) ^ 3) ≤
          riemannianVolumeMeasure ThreeModel
            (R.stage (H.activeStage (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)))).Carrier
            (H.stageMetric (H.activeStage (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)))
              ((t : ℝ) - (Real.sqrt (3 / 4) * r) ^ 2)) U ∧
        ∀ y ∈ U,
          IsLowActionEndpoint_C11Q R Bf t (clockSlice_C11Q R t (Real.sqrt (3 / 4) * r)) x (D A) y

/-- K5（block 形）的 `v_A = κ(A) e^{−D(A)} (4π)^{−3/2}`。 -/
def seedBlockVolumeConst_C11Q2 (D κ : ℝ → ℝ) (A : ℝ) : ℝ :=
  κ A * Real.exp (-D A) * (4 * Real.pi) ^ (-(3 / 2 : ℝ))

/-- **K5 ⇐ K4 + block**（不经 K0 / K5a）：block 的开集 + 已证的 K5 体积解释。 -/
theorem seedReducedVolumeLower_of_block_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₄ D κ : ℝ → ℝ}
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hK4 : BoundedReducedLengthNearSeed_C11Q F δ α nr C₄)
    (hB : SeedRegularBlock_C11Q2 F δ α nr C₄ D κ) :
    SeedReducedVolumeLower_C11Q F δ α nr (seedBlockVolumeConst_C11Q2 D κ) := by
  intro A hA
  refine ⟨by unfold seedBlockVolumeConst_C11Q2; have := hκ A hA; positivity, ?_⟩
  intro n H t p r hr hacc hsmall hvol x hx ϱ₀ hϱ₀ hball₀
  have hr0 : 0 < r := hsmall.1
  obtain ⟨b, hbt, hb, htraces⟩ := hsmall.2
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr0
  obtain ⟨seedTrace, -⟩ := htraces p hp
  obtain ⟨Bf, -, hfl⟩ := (F.tower.history n).exists_stageMetric_scalar_lower_bound
  have hBf : ScalarFloor_C11Q (F.tower.history n) Bf := hfl
  set w : ℝ := Real.sqrt (3 / 4) * r with hwdef
  have hs34 : 0 < Real.sqrt (3 / 4) := Real.sqrt_pos.2 (by norm_num)
  have hw : 0 < w := mul_pos hs34 hr0
  have hw2 : w ^ 2 = 3 / 4 * r ^ 2 := by
    rw [hwdef, mul_pow, Real.sq_sqrt (by norm_num)]
  have ht0 : (0 : ℝ) ≤ (t : ℝ) - w ^ 2 := by rw [hw2]; nlinarith
  have hsval : (clockSlice_C11Q (F.tower.history n) t w : ℝ) = (t : ℝ) - w ^ 2 :=
    clockSlice_val_C11Q (F.tower.history n) t ht0
  have hst : clockSlice_C11Q (F.tower.history n) t w ≤ t := by
    change (clockSlice_C11Q (F.tower.history n) t w : ℝ) ≤ (t : ℝ)
    rw [hsval]
    nlinarith [sq_nonneg w]
  let s₁ : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) - r ^ 2 / 2, ⟨by nlinarith, by have := t.2.2; nlinarith [sq_nonneg r]⟩⟩
  have hbs₁ : b ≤ s₁ := by
    change (b : ℝ) ≤ (t : ℝ) - r ^ 2 / 2
    rw [hb]
    nlinarith
  have hs₁t : s₁ ≤ t := by
    change (t : ℝ) - r ^ 2 / 2 ≤ (t : ℝ)
    nlinarith [sq_nonneg r]
  have hq₁ := hK4 A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf
    s₁ hbs₁ hs₁t rfl
  obtain ⟨U, hU, hvolU, hlow⟩ := hB A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀
    hϱ₀ hball₀ Bf hBf s₁ hbs₁ hs₁t rfl hq₁
  have hsq : Real.sqrt ((t : ℝ) - (clockSlice_C11Q (F.tower.history n) t w : ℝ)) = w := by
    rw [hsval, show (t : ℝ) - ((t : ℝ) - w ^ 2) = w ^ 2 by ring, Real.sqrt_sq hw.le]
  have hblock : ∀ q ∈ U,
      q ∈ H.regularMinimizerEndpoints (H.activeStage (clockSlice_C11Q (F.tower.history n) t w))
        (H.activeStage t) (H.activeStage_mono hst) t Bf w x ∧
      H.regularizedCost (H.activeStage (clockSlice_C11Q (F.tower.history n) t w))
        (H.activeStage t) (H.activeStage_mono hst) t Bf 0 w x q ≤
          ((2 * D A * w : ℝ) : WithTop ℝ) := by
    intro q hq
    obtain ⟨⟨hle', hmem⟩, hcost⟩ := hlow q hq
    unfold sliceCost_C11Q at hcost
    rw [dite_eq_left (H.activeStage_mono hst)] at hcost
    rw [hsq] at hmem hcost
    exact ⟨hmem, hcost⟩
  have hfinal := redVolume_ge_of_lowActionPatch_C11Q (F.tower.history n) hBf t x hw
    (H.activeStage_mono hst) U hU hvolU hblock
  unfold redVolTau_C11Q seedBlockVolumeConst_C11Q2
  rw [show 3 / 4 * r ^ 2 = w ^ 2 from hw2.symm, Real.sqrt_sq hw.le]
  exact hfinal

/-- **链（block 形 K5）**：WeightedMinBound + K3（`Λ ≥ e^{C/2+32/√2} + 1`）+ block ⇒
`LocalKappaWideSupply_C11Q`（K0、K1、K2、K5a 都不要）。 -/
theorem localKappa_of_weightedMinBound_block_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C Λ D κ : ℝ → ℝ}
    (hW : WeightedMinBound_C11Q2 F δ α nr C) (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A → weightedMinLevel_C11Q2 C A ≤ Λ A)
    (hB : SeedRegularBlock_C11Q2 F δ α nr (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A) :
    LocalKappaWideSupply_C11Q F δ α nr :=
  localKappaWide_of_seedReducedVolume_C11Q
    (seedReducedVolumeLower_of_block_C11Q2 hκ
      (boundedReducedLength_of_weightedMinBound_C11Q2 hW hK3 hΛ) hB)

/-- **链（block 形 K5 + G1 窗口 K3）**：剩余前提 = WeightedMinBound、block、K3 的显式数据与尺度前提
（在 `Λ = weightedMinLevel_C11Q2 C` 处）。 -/
theorem localKappa_of_weightedMinBound_block_window_C11Q2 {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    {nr C D κ : ℝ → ℝ}
    (hW : WeightedMinBound_C11Q2 F δ α nr C)
    (hB : SeedRegularBlock_C11Q2 F δ α nr (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (params : CutoffParameters)
    (records : ∀ n i, GeometricCutoffRecord (F.tower.history n).toHistory i params)
    (hcanon : ∀ n i b, ((records n i).static b).hasCanonicalWindow)
    (hδ : ∀ s, 0 ≤ s → params.delta s ≤ δ s) (hnr : ∀ t, 0 < t → 0 < nr t)
    (qcan ρbar : ℝ → ℝ) (hqcan : ∀ t, 0 < t → 0 < qcan t) (hρbar : ∀ t, 0 < t → 0 < ρbar t)
    (hneck : ∀ t s, 0 < t → t / 2 ≤ s → s ≤ t → params.neckRadius s ≤ ρbar t)
    (Ctime : ℝ≥0)
    (hderiv : ∀ n, ∀ (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (j : Fin ((F.tower.history n).toHistory.eventCount + 1))
      (y : ((F.tower.history n).toHistory.stage j).Carrier),
      (t : ℝ) / 2 ≤ (F.tower.history n).toHistory.time j →
      ∀ s ∈ Ioo ((F.tower.history n).toHistory.time j)
        ((F.tower.history n).toHistory.stageEndTime j), s < t.val →
        qcan t < metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y →
          |derivWithin (fun z => metricScalarAt ((F.tower.history n).toHistory.stageMetric j z) y)
              (Iic s) s| ≤
            Ctime * metricScalarAt ((F.tower.history n).toHistory.stageMetric j s) y ^ 2)
    (hscale : KappaWindowScale_C11Q2 P g params α nr (weightedMinLevel_C11Q2 C) qcan ρbar
      Ctime) :
    LocalKappaWideSupply_C11Q F δ α nr :=
  localKappa_of_weightedMinBound_block_C11Q2 hW
    (surgeryActionBarrier_of_window_C11Q2 params records hcanon hδ
      (fun A _ => weightedMinLevel_pos_C11Q2 C A) hnr qcan ρbar hqcan hρbar hneck Ctime hderiv
      hscale)
    (fun _ _ => le_rfl) hB hκ

/-- **consumer（G3）**：block 链 ⇒ P6B `hKappaLocal`（`L = 1`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C Λ D κ : ℝ → ℝ}
    (hW : WeightedMinBound_C11Q2 F δ α nr C) (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hΛ : ∀ A, 0 < A → weightedMinLevel_C11Q2 C A ≤ Λ A)
    (hB : SeedRegularBlock_C11Q2 F δ α nr (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A) :
    LocalKappaSupply_P6B F δ α nr :=
  (localKappa_of_weightedMinBound_block_C11Q2 hW hK3 hΛ hB hκ).toP6B

end GC.LongTime.Ch11
