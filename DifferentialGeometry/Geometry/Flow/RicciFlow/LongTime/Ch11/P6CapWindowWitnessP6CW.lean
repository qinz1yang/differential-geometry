import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageTransferP6ST2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapRestrictionPortC11P
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowCapWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCurvatureJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves

/-!
# S-a⁺ `hcapW`：age-0 cap-window witness（O-CH11-HCAPW G1，后缀 `_P6CW`）

`P6StageTransferP6ST2.stage_class_left_bad_P6ST2` 的 binder `hcapW`：record 的 cap 点
`(R.static b).inclusion ((R.static b).witness.cap x)` 处 output metric 的
`SpatialCanonicalWitness … ηout C1out C2out` + `capTubeHasNeckChart ηout`。

路线（T = 0，无新分析）：
* `exists_window_cap_spatialCanonicalWitness_of_standard_close`（`r := transitionEnd + 1`，`Θ := 0`）在
  `Q :=` 任一 standard solution、`T := 0`（`metric 0 = StandardCap.metric`）上用，`g :=` static cap 的 window
  metric 限制到子窗口 `standardCapWindow Dw`（C11P `restrictCanonicalWindow`）；整窗 closeness 由
  `metricDerivNorm_flat` + `restrictOpen_flat` + `metricDerivNorm_window_lt` 给出。
* 梯度界：`exists_presentedStaticCap_window_curvature_bounds`（`curvDerivNormSq 1 ≤ B q³`、`c q ≤ R`）+
  静态版 `abs_scalarDifferential_le_of_scaled_curvature_jet`（常值度量族）⇒ `Cgrad = n²√B/(c√c)`；
  `abs_mfderiv_metricScalarAt_localPullMetric_scaleMetric_le` 搬到 window metric（scale-invariant）。
* push 回 output：`pushforwardOfInjectiveULift`（compact ball 由 `exists_window_ball_placement` + lower
  comparison）再 `scaleMetric q⁻¹`，最后 `enlargeConstants`。
* cap 点落在 window 像里：`hasCanonicalWindow`（`IsCanonicalCutoffRecordFamily` 第 6 分量）。

常数：`Cs := max Cw Cgrad`（`Cw` 只依赖 `ηout`），需 `Cs ≤ C1out`、`Cs ≤ C2out`；参数阈值
`p.modelAccuracy ≤ εcap`、`Rcap ≤ p.modelRadius`、`mcap ≤ p.modelOrder`（`∃` 在 record 之前）。
无新 def / structure / 具名 Prop。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private local instance capWindowSigmaCompact_P6CW (D : ℝ) :
    SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

/-- 静态 scalar 梯度界（jet 形）：`curvDerivNormSq 1 g x ≤ q³ B`、`c q ≤ R_g(x)` ⇒
`|dR_g(v)| ≤ (n²√B/(c√c))·R^{3/2}·|v|`（常值度量族当 `SolutionOn`，套
`abs_scalarDifferential_le_of_scaled_curvature_jet`）。 -/
theorem abs_mfderiv_metricScalarAt_le_of_scaled_jet_P6CW {Q : OrientedThreeStage.{u}}
    (g : Q.Metric) {q B c : ℝ} (hq : 0 < q) (hc : 0 < c) (x : Q.Carrier)
    (hfirst : curvDerivNormSq 1 g x ≤ q ^ 3 * B) (hR : c * q ≤ metricScalarAt g x)
    (v : TangentSpace I3 x) :
    |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) x v)| ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt B / (c * Real.sqrt c) *
        metricScalarAt g x * Real.sqrt (metricScalarAt g x) * Real.sqrt (g.inner x v v) :=
  abs_scalarDifferential_le_of_scaled_curvature_jet
    (⟨⟨fun _ => g⟩⟩ : SolutionOn (I := I3) (M := Q.Carrier) (RealTimeInterval.univ 0))
    (t := 0) hq hc x hfirst hR v

namespace MetricCutCapEvent.PresentedStaticCap

/-- **S-a⁺（event 层）**：存在只依赖 `ε` 的常数 `Cs ≥ 1` 与参数阈值 `Rcap, mcap, εcap`，使得任一
带 `hasCanonicalWindow` 的 presented static cap（窗口半径 `≥ Rcap`、阶 `≥ mcap`、精度 `≤ εcap`）的每个
cap 点在 output metric 下都有 `SpatialCanonicalWitness ε C1 C2`（`Cs ≤ C1, C2`）且带
`capTubeHasNeckChart ε`。 -/
theorem exists_capWitness_of_standardClose_P6CW {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Cs Rcap : ℝ) (mcap : ℕ) (εcap : ℝ), 1 ≤ Cs ∧ 0 < εcap ∧
    ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
      {fixed : StaticCapScaffold} {D ε₀ : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
      (S : E.PresentedStaticCap fixed D m ε₀ b), S.hasCanonicalWindow →
      ε₀ ≤ εcap → Rcap ≤ D → mcap ≤ m →
      ∀ C1 C2 : ℝ, Cs ≤ C1 → Cs ≤ C2 → ∀ x : ThreeBall,
      ∃ W : SpatialCanonicalWitness E.outputMetric ε C1 C2 (S.inclusion (S.witness.cap x)),
        W.capTubeHasNeckChart ε := by
  obtain ⟨ε₀', c₀, B, hε₀', hc₀, hB, hjet⟩ :=
    exists_presentedStaticCap_window_curvature_bounds.{u}
  obtain ⟨S₀⟩ := standard_solution_nonempty
  obtain ⟨eta, heta, hlower⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison 0 le_rfl zero_lt_one
  obtain ⟨Cw, hCw, hM4⟩ := exists_window_cap_spatialCanonicalWitness_of_standard_close
    (r := StandardCap.transitionEnd + 1) (Θ := 0) hε hε' zero_lt_one
  obtain ⟨Λ, hΛ, hplace⟩ := StandardSolution.exists_window_ball_placement (Θ := 0) zero_lt_one
  set L := 4 * Cw + 1 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hΛL : 0 ≤ Λ * (L + 1) := by positivity
  obtain ⟨Dw, N, e, hrD, he, hwin⟩ := hM4 (Λ * (L + 1))
  set Cg : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt B / (c₀ * Real.sqrt c₀)
    with hCgdef
  have hTE : 0 < StandardCap.transitionEnd := StandardCap.transitionEnd_pos
  refine ⟨max Cw Cg, Dw + 1, max N 4, min (min e eta) ε₀', hCw.trans (le_max_left _ _),
    lt_min (lt_min he heta) hε₀', ?_⟩
  intro P Q a s E fixed D ε₀ m b S hS hacc hrad hord C1 C2 hC1 hC2 x
  have hεe : ε₀ ≤ e := hacc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεeta : ε₀ ≤ eta := hacc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεjet : ε₀ ≤ ε₀' := hacc.trans (min_le_right _ _)
  have hNm : N ≤ m := (le_max_left _ _).trans hord
  have h4m : 4 ≤ m := (le_max_right _ _).trans hord
  have hDw0 : 0 < Dw := by linarith
  have hDwD : Dw ≤ D := by linarith
  have hsub : standardCapWindow Dw ≤ standardCapWindow D :=
    fun _ hx => hx.trans_le (add_le_add hDwD (le_refl 1))
  -- cap 点落在 window 像里（`hasCanonicalWindow`）
  obtain ⟨u, hu, hux⟩ : ∃ u : standardCapWindow D, ‖u.val‖ ≤ StandardCap.transitionEnd ∧
      S.window u = S.inclusion (S.witness.cap x) := by
    obtain ⟨-, -, -, -, -, -, -, hcover⟩ := hS
    exact hcover x
  set S' := S.restrictCanonicalWindow hS hDw0 hDwD (le_refl m) (le_refl ε₀) with hS'def
  let z : standardCapWindow Dw := ⟨u.val, show ‖u.val‖ < Dw + 1 by linarith⟩
  have hz : ‖z.val‖ < StandardCap.transitionEnd + 1 := by
    change ‖u.val‖ < _
    linarith
  have hzS : S'.window z = S.inclusion (S.witness.cap x) := by
    rw [hS'def, restrictCanonicalWindow_window]
    exact hux
  have hq : 0 < S'.neck.scale := S'.neck.scale_pos
  -- 整窗 closeness（T = 0，标准解初值 = 标准帽）
  have hclose : ∀ i ≤ m, ∀ v : standardCapWindow Dw,
      metricDerivNorm i S'.witness.windowMetric
        ((S₀.val.metric 0).restrictOpen (standardCapWindow Dw))
        (StandardCap.metric.restrictOpen (standardCapWindow Dw)) v < ε₀ := by
    intro i hi v
    have hv : ‖v.val‖ < Dw + 1 := v.2
    have h := metricDerivNorm_flat hsub S.witness.windowMetric
      (StandardCap.metric.restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) i v
    rw [SmoothRiemannianMetric.restrictOpen_flat] at h
    rw [S₀.val.initial]
    exact h.trans_lt (S.metricDerivNorm_window_lt hi _ (show ‖v.val‖ < D by linarith))
  have hlow' : ∀ y : standardCapWindow Dw,
      (∀ v : TangentSpace (𝓡 3) y,
        (1 / 2) * ((S₀.val.metric 0).restrictOpen (standardCapWindow Dw)).inner y v v ≤
          S'.witness.windowMetric.inner y v v) ∧
      (1 / 2) * metricScalarAt ((S₀.val.metric 0).restrictOpen (standardCapWindow Dw)) y ≤
        metricScalarAt S'.witness.windowMetric y := fun y =>
    hlower S₀ _ _ 0 ⟨le_rfl, le_rfl⟩ y fun j hj =>
      (hclose j (by omega) y).le.trans hεeta
  have hzr : ‖(z : EuclideanSpace ℝ (Fin 3))‖ + Λ * (L + 1) < Dw + 1 := by
    have h := hz
    linarith
  obtain ⟨hcpt, -⟩ := hplace Dw L z hL0 hzr S₀ 0 ⟨le_rfl, le_rfl⟩ S'.witness.windowMetric
    (fun y v => (hlow' y).1 v)
  -- window metric = output metric 的 scaled local pull
  have hg : S'.witness.windowMetric = localPullMetric (scaleMetric S'.neck.scale hq E.outputMetric)
      S'.window S'.window_isLocalDiffeomorph := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, scaleMetric_inner]
    exact S'.window_inner y v w
  -- 梯度界（output metric，静态 jet）
  obtain ⟨hRout, hjout⟩ := hjet S' hεjet h4m z (show ‖z.val‖ < Dw by linarith)
  have hgradOut : ∀ w : TangentSpace I3 (S'.window z),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt E.outputMetric) (S'.window z) w)| ≤
        C2 * metricScalarAt E.outputMetric (S'.window z) *
          Real.sqrt (metricScalarAt E.outputMetric (S'.window z)) *
          Real.sqrt (E.outputMetric.inner (S'.window z) w w) := by
    intro w
    have h1 : curvDerivNormSq 1 E.outputMetric (S'.window z) ≤ S'.neck.scale ^ 3 * B :=
      (hjout 1 (by norm_num)).trans_eq (by ring)
    have hR0 : 0 ≤ metricScalarAt E.outputMetric (S'.window z) :=
      le_trans (by positivity) hRout
    have hCgC2 : Cg ≤ C2 := (le_max_right _ _).trans hC2
    refine (abs_mfderiv_metricScalarAt_le_of_scaled_jet_P6CW E.outputMetric hq hc₀ _ h1 hRout
      w).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCgC2 hR0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hgradG := abs_mfderiv_metricScalarAt_localPullMetric_scaleMetric_le E.outputMetric
    S'.window S'.window_isLocalDiffeomorph hq z hgradOut
  -- 标准帽 witness（window metric 上）
  have key : ∃ W : SpatialCanonicalWitness (localPullMetric (scaleMetric S'.neck.scale hq
      E.outputMetric) S'.window S'.window_isLocalDiffeomorph) ε Cw C2 z,
      W.capTubeHasNeckChart ε ∧ 2 * W.radius < L := by
    rw [← hg]
    have hgradG' : ∀ v : TangentSpace I3 z,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt S'.witness.windowMetric) z v)| ≤
          C2 * metricScalarAt S'.witness.windowMetric z *
            Real.sqrt (metricScalarAt S'.witness.windowMetric z) *
            Real.sqrt (S'.witness.windowMetric.inner z v v) := by
      rw [hg]
      exact hgradG
    obtain ⟨W, hW, -⟩ := hwin S₀ 0 ⟨le_rfl, le_rfl⟩ S'.witness.windowMetric
      (fun i hi v => (hclose i (hi.trans hNm) v).trans_le hεe) z hz C2
      ((le_max_left _ _).trans hC2) hgradG'
    refine ⟨W, hW, ?_⟩
    have hQ1 : 1 ≤ metricScalarAt (S₀.val.metric 0) z.val :=
      S₀.val.one_le_scalar 0 (S₀.mem_domain_of_mem_Icc zero_lt_one ⟨le_rfl, le_rfl⟩) z.val
    have hlowz := (hlow' z).2
    rw [metricScalarAt_restrictOpen] at hlowz
    have hRS : 1 / 2 ≤ metricScalarAt S'.witness.windowMetric z := by
      linarith only [hlowz, hQ1]
    have hs : 1 / 2 ≤ Real.sqrt (metricScalarAt S'.witness.windowMetric z) := by
      have h := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ^ 2 ≤
        metricScalarAt S'.witness.windowMetric z by linarith only [hRS])
      rwa [Real.sqrt_sq (by norm_num)] at h
    have hr0 : 0 ≤ W.radius :=
      (inv_nonneg.mpr (Real.sqrt_nonneg _)).trans W.radius_lower
    have hup := W.radius_upper
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by linarith only [hRS]))] at hup
    linarith only [mul_le_mul_of_nonneg_left hs hr0, hup, hLdef]
  obtain ⟨W, hW, hWr⟩ := key
  rw [hg] at hcpt
  have hinj : Function.Injective S'.window := S'.window_smooth.isEmbedding.injective
  have hscale : scaleMetric S'.neck.scale⁻¹ (inv_pos.mpr hq)
      (scaleMetric S'.neck.scale hq E.outputMetric) = E.outputMetric :=
    SmoothRiemannianMetric.ext_inner fun v w₁ w₂ => by
      simp only [scaleMetric_inner]
      field_simp
  have hC1' : Cw ≤ C1 := (le_max_left _ _).trans hC1
  rw [← hzS, ← hscale]
  exact ⟨((W.pushforwardOfInjectiveULift S'.window_isLocalDiffeomorph hinj hWr hcpt).scaleMetric
      S'.neck.scale⁻¹ (inv_pos.mpr hq)).enlargeConstants hC1' le_rfl,
    (SpatialCanonicalWitness.capTubeHasNeckChart.scaleMetric S'.neck.scale⁻¹ (inv_pos.mpr hq)
      (hW.pushforwardOfInjectiveULift S'.window_isLocalDiffeomorph hinj hWr hcpt)).enlarge_constants
      hC1' le_rfl⟩

end MetricCutCapEvent.PresentedStaticCap

namespace GeometricCutoffRecord

/-- **`hcapW_of_standardClose_P6CW`（record 层，S-a⁺）**：常数 `Cs ≥ 1`（只依赖 `ε`）与参数阈值
`Rcap, mcap, εcap` 先取；之后对任一 record `R`（`∀ b, (R.static b).hasCanonicalWindow`，参数满足三阈值）
与任意 `C1out, C2out ≥ Cs`，得到 `stage_class_left_bad_P6ST2` 的 `hcapW` 槽的逐字形。 -/
theorem hcapW_of_standardClose_P6CW {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Cs Rcap : ℝ) (mcap : ℕ) (εcap : ℝ), 1 ≤ Cs ∧ 0 < εcap ∧
    ∀ {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
      (R : GeometricCutoffRecord H i p), (∀ b, (R.static b).hasCanonicalWindow) →
      p.modelAccuracy ≤ εcap → Rcap ≤ p.modelRadius → mcap ≤ p.modelOrder →
      ∀ C1out C2out : ℝ, Cs ≤ C1out → Cs ≤ C2out →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
        ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1out C2out
          ((R.static b).inclusion ((R.static b).witness.cap x)), W.capTubeHasNeckChart ε := by
  obtain ⟨Cs, Rcap, mcap, εcap, hCs, hεcap, hev⟩ :=
    MetricCutCapEvent.PresentedStaticCap.exists_capWitness_of_standardClose_P6CW.{u} hε hε'
  exact ⟨Cs, Rcap, mcap, εcap, hCs, hεcap,
    fun R hcan hacc hrad hord C1out C2out h1 h2 b x =>
      hev (R.static b) (hcan b) hacc hrad hord C1out C2out h1 h2 x⟩

/-- **consumer（单个 record）**：`stage_class_left_bad_P6ST2` 的 `hcapW` 槽由
`hcapW_of_standardClose_P6CW` 供给；剩余输入 = `hcan`、三个参数阈值、`Cs ≤ C1out, C2out`、`hfoot`、`hsel`。 -/
theorem stage_class_left_bad_canonical_P6CW {ηout : ℝ} (hη : 0 < ηout) (hη' : ηout < 1 / 11) :
    ∃ (Cs Rcap : ℝ) (mcap : ℕ) (εcap : ℝ), 1 ≤ Cs ∧ 0 < εcap ∧
    ∀ {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
      (R : GeometricCutoffRecord H i p), (∀ b, (R.static b).hasCanonicalWindow) →
      p.modelAccuracy ≤ εcap → Rcap ≤ p.modelRadius → mcap ≤ p.modelOrder →
      ∀ {ηfine C1 C2 m C1out C2out : ℝ} {k : ℕ} {Ctime : ℝ≥0},
      Cs ≤ C1out → Cs ≤ C2out → 2 * C1 ≤ C1out → 1000 * C2 ≤ C2out →
      ηfine ≤ neckModelTolerance (ηout / 2) →
      ∀ {y : (H.stageAt (H.stageTime i.succ)).Carrier},
      (∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
        (H.event i).RegularCrossing p' q →
        Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ηout C1 C2 m k)) →
      ¬ H.HasSpatialCanonicalTimeControl ηout C1out C2out Ctime (H.stageTime i.succ) y →
      LeftBadAt_CXST (fun v : Icc (0 : ℝ) H.horizon => (v : ℝ))
        (fun v z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v)
          ηfine C1 C2 z, W.capTubeHasNeckChart ηfine ∧ W.HasMargins m) (H.time i.succ) := by
  obtain ⟨Cs, Rcap, mcap, εcap, hCs, hεcap, hcapW⟩ := hcapW_of_standardClose_P6CW.{u} hη hη'
  exact ⟨Cs, Rcap, mcap, εcap, hCs, hεcap,
    fun R hcan hacc hrad hord _ _ _ _ _ _ _ _ hC1 hC2 h1 h2 hle _ hfoot hsel =>
      R.stage_class_left_bad_P6ST2 h1 h2 hle
        (hcapW R hcan hacc hrad hord _ _ hC1 hC2) hfoot hsel⟩

end GeometricCutoffRecord

/-- 三个参数阈值在 late-wire 形（`modelAccuracy ≤ 1/(n+1)`、`n+1 ≤ modelRadius`、`n+2 ≤ modelOrder`）下
eventually 成立。 -/
theorem eventually_params_of_lateWire_P6CW {p : ℕ → CutoffParameters} {Rcap εcap : ℝ}
    {mcap : ℕ} (hεcap : 0 < εcap)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder) :
    ∀ᶠ n in atTop, (p n).modelAccuracy ≤ εcap ∧ Rcap ≤ (p n).modelRadius ∧
      mcap ≤ (p n).modelOrder := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / εcap)
  have hN0' : 1 < (N0 : ℝ) * εcap := (div_lt_iff₀ hεcap).mp hN0
  filter_upwards [eventually_ge_atTop N0, eventually_ge_atTop mcap,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop Rcap] with n hn hm hR
  have hn' : (N0 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨(hacc n).trans ?_, hR.trans (by linarith [hrad n]), hm.trans (by have := hord n; omega)⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **late-wire 形的 eventual 供给**：K 层 late records（`recordsK n i hi`，`hi : T₀ n ≤ time i.succ`）带
`hcanK` 与 late-wire 参数（`exists_lateThr_free_P6WR` 的前四个合取项逐字形）⇒ eventually（`n` 大到
`1/(n+1) ≤ εcap`、`Rcap ≤ n+1`、`mcap ≤ n+2`）**对所有 late record** 有 `hcapW`。 -/
theorem eventually_hcapW_of_lateWire_P6CW {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ {Kh : ℕ → ObservedHistory.{u}} {p : ℕ → CutoffParameters}
      {T₀ : ℕ → ℝ} (recordsK : ∀ n (i : Fin (Kh n).eventCount),
        T₀ n ≤ (Kh n).time i.succ → GeometricCutoffRecord (Kh n) i (p n)),
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      ∀ C1out C2out : ℝ, Cs ≤ C1out → Cs ≤ C2out →
      ∀ᶠ n in atTop, ∀ i hi (b : ((Kh n).event i).RetainedBoundaryIndex) (x : ThreeBall),
        ∃ W : SpatialCanonicalWitness ((Kh n).event i).outputMetric ε C1out C2out
          (((recordsK n i hi).static b).inclusion (((recordsK n i hi).static b).witness.cap x)),
          W.capTubeHasNeckChart ε := by
  obtain ⟨Cs, Rcap, mcap, εcap, hCs, hεcap, hcapW⟩ :=
    GeometricCutoffRecord.hcapW_of_standardClose_P6CW.{u} hε hε'
  refine ⟨Cs, hCs, fun recordsK hcan hacc hrad hord C1out C2out h1 h2 => ?_⟩
  filter_upwards [eventually_params_of_lateWire_P6CW (Rcap := Rcap) (mcap := mcap) hεcap hacc
    hrad hord] with n hn
  intro i hi b x
  exact hcapW (recordsK n i hi) (hcan n i hi) hn.1 hn.2.1 hn.2.2 C1out C2out h1 h2 b x

/-- **consumer（K 层 stage 序列，eventual）**：late-wire 数据 + `hfoot` eventually ⇒ eventually 每个
stage 左侧有任意近的 fine-margin 坏点（`stage_class_left_bad_P6ST2` 的 `hcapW` 槽由
`eventually_hcapW_of_lateWire_P6CW` 填）。 -/
theorem stage_class_left_bad_eventually_lateWire_P6CW {ηout : ℝ} (hη : 0 < ηout)
    (hη' : ηout < 1 / 11) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ {Kh : ℕ → ObservedHistory.{u}} {p : ℕ → CutoffParameters}
      {T₀ : ℕ → ℝ} (recordsK : ∀ n (i : Fin (Kh n).eventCount),
        T₀ n ≤ (Kh n).time i.succ → GeometricCutoffRecord (Kh n) i (p n)),
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
      (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
      ∀ {i : ∀ n, Fin (Kh n).eventCount}, (∀ n, T₀ n ≤ (Kh n).time (i n).succ) →
      ∀ {ηfine C1 C2 m C1out C2out : ℝ} {k : ℕ} {Ctime : ℝ≥0},
      Cs ≤ C1out → Cs ≤ C2out → 2 * C1 ≤ C1out → 1000 * C2 ≤ C2out →
      ηfine ≤ neckModelTolerance (ηout / 2) →
      ∀ (y : ∀ n, ((Kh n).stageAt ((Kh n).stageTime (i n).succ)).Carrier),
      (∀ᶠ n in atTop, ∀ (p' : ((Kh n).stage (i n).castSucc).Carrier)
        (q : ((Kh n).stage (i n).succ).Carrier), HEq (y n) q →
        ((Kh n).event (i n)).RegularCrossing p' q →
        Nonempty (((Kh n).event (i n)).BufferedFootprintData_P6ST2 p' q ηout C1 C2 m k)) →
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ηout C1out C2out Ctime
        ((Kh n).stageTime (i n).succ) (y n)) →
      ∀ᶠ n in atTop, LeftBadAt_CXST (fun v : Icc (0 : ℝ) (Kh n).horizon => (v : ℝ))
        (fun v z => ¬ ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v)
          ηfine C1 C2 z, W.capTubeHasNeckChart ηfine ∧ W.HasMargins m)
        ((Kh n).time (i n).succ) := by
  obtain ⟨Cs, hCs, hev⟩ := eventually_hcapW_of_lateWire_P6CW.{u} hη hη'
  refine ⟨Cs, hCs, fun recordsK hcan hacc hrad hord i hi _ _ _ _ _ _ _ _ hC1 hC2 h1 h2 hle y
    hfoot hsel => ?_⟩
  filter_upwards [hfoot, hev recordsK hcan hacc hrad hord _ _ hC1 hC2] with n hn hcapW
  exact (recordsK n (i n) (hi n)).stage_class_left_bad_P6ST2 h1 h2 hle
    (hcapW (i n) (hi n)) hn (hsel n)

/-- canonical record family 自带 `hasCanonicalWindow`（`IsCanonicalCutoffRecordFamily` 第 6 分量）。 -/
theorem hasCanonicalWindow_of_family_P6CW {H : RetainedCoreHistory.{u}} {p₀ p : CutoffParameters}
    {δ₀ ρ₀ : ℝ} {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records) (i : Fin H.eventCount) :
    ∀ b, ((records i).static b).hasCanonicalWindow :=
  hrec.2.2.2.2.2.1 i

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
