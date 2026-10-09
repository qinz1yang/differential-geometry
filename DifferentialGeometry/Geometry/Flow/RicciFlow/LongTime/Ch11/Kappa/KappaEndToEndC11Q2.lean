import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedBlockC11Q2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaDiagonalAlignP6D2

/-!
# 局部 κ 线端到端（O-CH11-KAPPA2 G4，后缀 `_C11Q2`）

K0–K6（K0 / K4 / K5 / K6 已证，K3 窗口化，K5 block 形）+ native 数据 ⇒ `LocalKappaWideSupply_C11Q`
⇒（S7 + Q3）`nr := 0` window ⇒ `Pre841Data_C11K`（PRE841 `pre841Data_of_window_C11K`）⇒（P6D2 慢对角化）
M8 极限 `κ/250`-noncollapsed。

* **K3 的数据部分由 native 数据供给**（`surgeryActionBarrier_of_native_C11Q2`）：
  `Pre841NativeData_C11K`（全下标版 `N`）的 `params / records / canonical_windows` 即窗口屏障的 records；
  `nr := neckRadius`、`ρ̄(t) := neckRadius(t/2)`、`qcan(t) := neckRadius(t)⁻²`（`radius_antitone`）；
  窗口导数控制由 `time_derivative_event / _final` 换到 `stageMetric` 形
  （`stageScalarDeriv_of_native_C11Q2`）。K3 只剩**尺度前提** `KappaWindowScale_C11Q2`。
* 端到端：`localKappaWideSupply_of_native_C11Q2`、`nonempty_pre841Data_of_native_C11Q2`；M8 consumer
  （`exists_local_ancient_limit_kappa_noncollapsed_of_kseq_P6D2` 吃 `d.volume_ge`）。

## 局部 κ 线现在只差的显式前提（`nonempty_pre841Data_of_native_C11Q2` 的前提，逐条）
1. `hW : WeightedMinBound_C11Q2 F δ α nr C`——astra weighted-minimum 链积分形（实际定理：donor
   `PreparedSpatialPositivePoleWeightedPropagation` 等在**其构造的** surgery 内给；对一般 `F` 的版本须由
   `DistinctPoleWeightedTemporalSupport / ClosedEventWeightedMinimum` 积分出来；对齐 `weightedMinBound_of_
   traced_C11Q2` 已写好）；
2. `hB : SeedRegularBlock_C11Q2 …`——URE 结论形（URE 未落地；其输入 `hWindow` / node 数据是 K3 窗口数据的
   astra 版）；
3. `hscale : KappaWindowScale_C11Q2 …`——**δ₀ 尺度引理**（树内屏障常数 `ε₀, R₀, m₀` 对 `t` 一致）；
4. 数据：全下标 native `N`（`Pre841NativeData_C11K`）、`params.delta ≤ δ`、S7 `hacc`、Q3 小尺度
   `hsmallScale`（SMALLVOL）、Pre841 的种子 / 窗口 / 距离数据（PRE841 原有前提）。
**不再需要**：K0（已证）、K1、K2（被积分形旁路）、K5a（被 block 旁路）、K6（已证）。
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

/-! ## 1. native 数据 ⇒ K3 的数据部分 -/

/-- native 的 slab 形时间导数控制 ⇒ `stageMetric` 形（阈值 `neckRadius(s)⁻²`）。 -/
theorem stageScalarDeriv_of_native_C11Q2 {H : ℕ → ObservedHistory.{u}}
    (N : Pre841NativeData_C11K H) (n : ℕ) (j : Fin ((H n).eventCount + 1))
    (y : ((H n).stage j).Carrier) (s : ℝ) (hs : s ∈ Ioo ((H n).time j) ((H n).stageEndTime j))
    (hq : (N.params.neckRadius s ^ 2)⁻¹ < metricScalarAt ((H n).stageMetric j s) y) :
    |derivWithin (fun z => metricScalarAt ((H n).stageMetric j z) y) (Iic s) s| ≤
      N.Ctime * metricScalarAt ((H n).stageMetric j s) y ^ 2 := by
  cases j using Fin.lastCases with
  | cast i =>
    have hmetric : (H n).stageMetric i.castSucc = ((H n).event i).incoming.flow.base.metric := by
      funext τ
      simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]
    rw [hmetric] at hq ⊢
    rw [(H n).stageEndTime_castSucc] at hs
    exact N.time_derivative_event n i y s hs hq
  | last =>
    have hlt : (H n).time (Fin.last (H n).eventCount) < (H n).horizon := by
      simpa only [(H n).stageEndTime_last] using hs.1.trans hs.2
    have hmetric : (H n).stageMetric (Fin.last (H n).eventCount) =
        ((H n).finalSlab hlt).flow.base.metric := by
      funext τ
      simp only [ObservedHistory.stageMetric, Fin.lastCases_last, dite_eq_left hlt]
    rw [hmetric] at hq ⊢
    rw [(H n).stageEndTime_last] at hs
    exact N.time_derivative_final n hlt y s hs hq

/-- **K3 由 native 数据 + 尺度前提**：`nr := neckRadius`、`ρ̄(t) := neckRadius(t/2)`、
`qcan(t) := neckRadius(t)⁻²`。 -/
theorem surgeryActionBarrier_of_native_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {Λ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s) (hΛ : ∀ A, 0 < A → 0 < Λ A)
    (hscale : KappaWindowScale_C11Q2 P g N.params α N.params.neckRadius Λ
      (fun t => (N.params.neckRadius t ^ 2)⁻¹) (fun t => N.params.neckRadius (t / 2)) N.Ctime) :
    SurgeryActionBarrier_C11Q F δ α N.params.neckRadius Λ := by
  refine surgeryActionBarrier_of_window_C11Q2 N.params N.records N.canonical_windows hδ hΛ
    (fun t ht => N.params.neckRadius_pos t ht.le) _ _
    (fun t ht => inv_pos.mpr (pow_pos (N.params.neckRadius_pos t ht.le) 2))
    (fun t ht => N.params.neckRadius_pos (t / 2) (by positivity)) ?_ N.Ctime ?_ hscale
  · intro t s ht hs1 _
    have ht2 : (0 : ℝ) ≤ t / 2 := by positivity
    exact N.radius_antitone (show t / 2 ∈ Ici (0 : ℝ) from ht2)
      (show s ∈ Ici (0 : ℝ) from ht2.trans hs1) hs1
  · intro n t j y _ s hs hst hq
    refine stageScalarDeriv_of_native_C11Q2 N n j y s hs (lt_of_le_of_lt ?_ hq)
    have hs0 : 0 ≤ s := ((F.tower.history n).toHistory.time_nonneg j).trans hs.1.le
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have hρt := N.params.neckRadius_pos t ht0
    have hanti : N.params.neckRadius t ≤ N.params.neckRadius s :=
      N.radius_antitone (show s ∈ Ici (0 : ℝ) from hs0) (show (t : ℝ) ∈ Ici (0 : ℝ) from ht0)
        hst.le
    exact inv_anti₀ (pow_pos hρt 2) (pow_le_pow_left₀ hρt.le hanti 2)

/-! ## 2. 端到端 -/

/-- **局部 κ（尺度 ≥ neckRadius/100）由 native 数据**：WeightedMinBound + block + 尺度前提
（`Λ = weightedMinLevel_C11Q2 C`）⇒ `LocalKappaWideSupply_C11Q F δ α neckRadius`。 -/
theorem localKappaWideSupply_of_native_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {C D κ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hW : WeightedMinBound_C11Q2 F δ α N.params.neckRadius C)
    (hB : SeedRegularBlock_C11Q2 F δ α N.params.neckRadius (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hscale : KappaWindowScale_C11Q2 P g N.params α N.params.neckRadius
      (weightedMinLevel_C11Q2 C) (fun t => (N.params.neckRadius t ^ 2)⁻¹)
      (fun t => N.params.neckRadius (t / 2)) N.Ctime) :
    LocalKappaWideSupply_C11Q F δ α N.params.neckRadius :=
  localKappa_of_weightedMinBound_block_C11Q2 hW
    (surgeryActionBarrier_of_native_C11Q2 N hδ (fun A _ => weightedMinLevel_pos_C11Q2 C A)
      hscale)
    (fun _ _ => le_rfl) hB hκ

/-- **端到端 ⇒ `Pre841Data_C11K`**：上一定理 + S7（`hacc`）+ Q3 小尺度（`hsmallScale`，SMALLVOL 的显式形，
`nr = neckRadius`）⇒ `nr := 0` window（`localKappaWindow_zero_of_window_and_small_C11V`）⇒ 沿子列 `ind`
（native `N.comp ind`）的 `Pre841Data_C11K`。 -/
theorem nonempty_pre841Data_of_native_C11Q2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {C D κ : ℝ → ℝ}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (hW : WeightedMinBound_C11Q2 F δ α N.params.neckRadius C)
    (hB : SeedRegularBlock_C11Q2 F δ α N.params.neckRadius (weightedMinLengthConst_C11Q2 C) D κ)
    (hκ : ∀ A, 0 < A → 0 < κ A)
    (hδ : ∀ s, 0 ≤ s → N.params.delta s ≤ δ s)
    (hscale : KappaWindowScale_C11Q2 P g N.params α N.params.neckRadius
      (weightedMinLevel_C11Q2 C) (fun t => (N.params.neckRadius t ^ 2)⁻¹)
      (fun t => N.params.neckRadius (t / 2)) N.Ctime)
    (hacc : LargerBallAccuracySupply_C11S δ α) {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallScale : ∃ T : ℝ, 0 < T ∧
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
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < N.params.neckRadius v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n)) :
    Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  have hloc : LocalKappaSupply_P6B F δ α N.params.neckRadius :=
    (localKappaWideSupply_of_native_C11Q2 N hW hB hκ hδ hscale).toP6B
  obtain ⟨κ₁, hκ₁, hW₁⟩ :=
    localKappaWindow_of_late_P6B (localKappaLateSupply_of_envelope_P6B hacc hloc) A hA
  have hW0 := localKappaWindow_zero_of_window_and_small_C11V hW₁ hsmallScale
  exact ⟨pre841Data_of_window_C11K (lt_min hκ₁ hκ') hW0 ind (N.comp ind) t p r hlate htime hsmall
    hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist⟩

/-- **consumer（G4，M8）**：任一 `Pre841Data_C11K`（如上一定理所给）⇒ P6D2 慢对角化 ⇒ M8：极限
`d.kappa/250`-noncollapsed（`d.volume_ge` 原样喂 `hK`）。 -/
example {H : ℕ → ObservedHistory.{u}} {t : ∀ n, Icc (0 : ℝ) (H n).horizon}
    {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n}
    (d : Pre841Data_C11K H t y R hR)
    (hRlim : Tendsto R atTop atTop)
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (R n))))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v)
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)))
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt))))) :=
  ObservedHistory.exists_local_ancient_limit_kappa_noncollapsed_of_kseq_P6D2 H t y R hR hRlim
    htraced hr₀ hw hseed d.kappa_pos d.volume_ge hPhi hpinch

end GC.LongTime.Ch11
