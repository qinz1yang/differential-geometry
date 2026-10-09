import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapWindowWitnessP6CW

/-!
# collar 扩展 `hcapW`：窗口内区 `‖x‖ ≤ transitionEnd + 10` 的 canonical witness（O-CH11-HCENP G1，后缀 `_P6HE`）

HCAPW `exists_capWitness_of_standardClose_P6CW`（`P6CapWindowWitnessP6CW.lean:72`）只给 cap 点
`S.inclusion (S.witness.cap x)`（`‖u‖ ≤ transitionEnd`）。`surgery_no_shortcut_C11D` 的端点保护要的是
**窗口内区** `S.window '' {‖x‖ ≤ transitionEnd + 10}` 之外，因此坏点不在内区需要 `hsel` ⇒ 内区点是 canonical
witness 点（collar 点）。本文件把 HCAPW 的证明逐字搬到窗口点：

* 唯一改动 1：`r := transitionEnd + 11`（模板 `r := transitionEnd + 1`；底层
  `exists_window_cap_spatialCanonicalWitness_of_standard_close` 本来就对任意 `r` 成立）；
* 唯一改动 2：去掉模板的 "cap 点落在 window 像里" 一步（`hasCanonicalWindow` 的 cover 分量），直接取窗口点
  `z := x`，`‖x‖ ≤ transitionEnd + 10 < r < Dw`；其余（`restrictCanonicalWindow`、`hclose`、`hlow'`、
  `hplace`、梯度界、push 回 output）对任意窗口点成立，原样复制。
* 额外导出 `transitionEnd + 10 < Rcap`（`Rcap = Dw + 1`，`hrD : r + Λ(L+1) < Dw`），供
  `surgery_no_shortcut_C11D` 的 `hD`。

常数 `Cs′ = max Cw′ Cgrad`（`Cw′ = 1000·Cs(r)` 随 `r` 变，`Cgrad` 同 HCAPW）。`capCollarCs_P6HE ε` 是闭项
（`Classical.choose`，同 `p6CapCs_C11GT6` 的写法），`capCollarCs_spec_P6HE` 是 spec。**`capCollarCs ε` 与
`p6CapCs ε` 是两个 `∃` 的 choice，没有大小关系**（见 `state-O-CH11-HCENP.md` G0 R1）。
无新 structure / 具名 Prop。
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

private local instance capCollarSigmaCompact_P6HE (D : ℝ) :
    SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

namespace MetricCutCapEvent.PresentedStaticCap

/-- **collar 扩展 hcapW（event 层，`_P6HE`）**：存在只依赖 `ε` 的常数 `Cs ≥ 1` 与参数阈值
`Rcap, mcap, εcap`（`transitionEnd + 10 < Rcap`），使得任一带 `hasCanonicalWindow` 的 presented static cap
（窗口半径 `≥ Rcap`、阶 `≥ mcap`、精度 `≤ εcap`）的每个窗口内区点 `‖x‖ ≤ transitionEnd + 10` 在 output
metric 下都有 `SpatialCanonicalWitness ε C1 C2`（`Cs ≤ C1, C2`）且带 `capTubeHasNeckChart ε`。 -/
theorem exists_collarWitness_of_standardClose_P6HE {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Cs Rcap : ℝ) (mcap : ℕ) (εcap : ℝ), 1 ≤ Cs ∧ 0 < εcap ∧
    StandardCap.transitionEnd + 10 < Rcap ∧
    ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
      {fixed : StaticCapScaffold} {D ε₀ : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
      (S : E.PresentedStaticCap fixed D m ε₀ b), S.hasCanonicalWindow →
      ε₀ ≤ εcap → Rcap ≤ D → mcap ≤ m →
      ∀ C1 C2 : ℝ, Cs ≤ C1 → Cs ≤ C2 →
      ∀ x : standardCapWindow D, ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      ∃ W : SpatialCanonicalWitness E.outputMetric ε C1 C2 (S.window x),
        W.capTubeHasNeckChart ε := by
  obtain ⟨ε₀', c₀, B, hε₀', hc₀, hB, hjet⟩ :=
    exists_presentedStaticCap_window_curvature_bounds.{u}
  obtain ⟨S₀⟩ := standard_solution_nonempty
  obtain ⟨eta, heta, hlower⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison 0 le_rfl zero_lt_one
  obtain ⟨Cw, hCw, hM4⟩ := exists_window_cap_spatialCanonicalWitness_of_standard_close
    (r := StandardCap.transitionEnd + 11) (Θ := 0) hε hε' zero_lt_one
  obtain ⟨Λ, hΛ, hplace⟩ := StandardSolution.exists_window_ball_placement (Θ := 0) zero_lt_one
  set L := 4 * Cw + 1 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hΛL : 0 ≤ Λ * (L + 1) := by positivity
  obtain ⟨Dw, N, e, hrD, he, hwin⟩ := hM4 (Λ * (L + 1))
  set Cg : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt B / (c₀ * Real.sqrt c₀)
    with hCgdef
  have hTE : 0 < StandardCap.transitionEnd := StandardCap.transitionEnd_pos
  refine ⟨max Cw Cg, Dw + 1, max N 4, min (min e eta) ε₀', hCw.trans (le_max_left _ _),
    lt_min (lt_min he heta) hε₀', by linarith, ?_⟩
  intro P Q a s E fixed D ε₀ m b S hS hacc hrad hord C1 C2 hC1 hC2 x hx
  have hεe : ε₀ ≤ e := hacc.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεeta : ε₀ ≤ eta := hacc.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεjet : ε₀ ≤ ε₀' := hacc.trans (min_le_right _ _)
  have hNm : N ≤ m := (le_max_left _ _).trans hord
  have h4m : 4 ≤ m := (le_max_right _ _).trans hord
  have hDw0 : 0 < Dw := by linarith
  have hDwD : Dw ≤ D := by linarith
  have hsub : standardCapWindow Dw ≤ standardCapWindow D :=
    fun _ hx => hx.trans_le (add_le_add hDwD (le_refl 1))
  set S' := S.restrictCanonicalWindow hS hDw0 hDwD (le_refl m) (le_refl ε₀) with hS'def
  let z : standardCapWindow Dw := ⟨x.val, show ‖x.val‖ < Dw + 1 by linarith⟩
  have hz : ‖z.val‖ < StandardCap.transitionEnd + 11 := by
    change ‖x.val‖ < _
    linarith
  have hzS : S'.window z = S.window x := by
    rw [hS'def, restrictCanonicalWindow_window]
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-! ## 闭项常数 `capCollarCs_P6HE` 与 record 层 -/

namespace GC.LongTime.Ch11

universe u

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

/-- **collar 常数** `Cs′(η) = max Cw′ Cgrad`：`exists_collarWitness_of_standardClose_P6HE` 的 `∃ Cs`
（只依赖 `η`；`η ∉ (0, 1/11)` 时取 `1`）。与 `p6CapCs_C11GT6` 是**不同的** `Classical.choose`，
二者没有大小关系。 -/
def capCollarCs_P6HE (η : ℝ) : ℝ :=
  if h : 0 < η ∧ η < 1 / 11 then
    Classical.choose
      (MetricCutCapEvent.PresentedStaticCap.exists_collarWitness_of_standardClose_P6HE.{u}
        h.1 h.2)
  else 1

/-- **collar spec（event 层）**：`Cs := capCollarCs_P6HE ε` 时 `exists_collarWitness_…` 的结论成立。 -/
theorem capCollarCs_spec_P6HE {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Rcap : ℝ) (mcap : ℕ) (εcap : ℝ), 1 ≤ capCollarCs_P6HE.{u} ε ∧ 0 < εcap ∧
    StandardCap.transitionEnd + 10 < Rcap ∧
    ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
      {fixed : StaticCapScaffold} {D ε₀ : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
      (S : E.PresentedStaticCap fixed D m ε₀ b), S.hasCanonicalWindow →
      ε₀ ≤ εcap → Rcap ≤ D → mcap ≤ m →
      ∀ C1 C2 : ℝ, capCollarCs_P6HE.{u} ε ≤ C1 → capCollarCs_P6HE.{u} ε ≤ C2 →
      ∀ x : standardCapWindow D, ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
      ∃ W : SpatialCanonicalWitness E.outputMetric ε C1 C2 (S.window x),
        W.capTubeHasNeckChart ε := by
  unfold capCollarCs_P6HE
  rw [dite_eq_left ⟨hε, hε'⟩]
  exact Classical.choose_spec
    (MetricCutCapEvent.PresentedStaticCap.exists_collarWitness_of_standardClose_P6HE.{u} hε hε')

/-- **collar spec（record 层，G1 主定理）**：常数取闭项 `capCollarCs_P6HE ε`；任一 record `R`
（`∀ b, (R.static b).hasCanonicalWindow`，参数满足三阈值）与 `C1, C2 ≥ capCollarCs_P6HE ε`，
每个 static cap 的窗口内区点 `‖x‖ ≤ transitionEnd + 10` 在 `outputMetric` 下有 canonical witness
且带 `capTubeHasNeckChart ε`。 -/
theorem capCollar_of_record_P6HE {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Rcap : ℝ) (mcap : ℕ) (εcap : ℝ), 1 ≤ capCollarCs_P6HE.{u} ε ∧ 0 < εcap ∧
    StandardCap.transitionEnd + 10 < Rcap ∧
    ∀ {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
      (R : GeometricCutoffRecord H i p), (∀ b, (R.static b).hasCanonicalWindow) →
      p.modelAccuracy ≤ εcap → Rcap ≤ p.modelRadius → mcap ≤ p.modelOrder →
      ∀ C1 C2 : ℝ, capCollarCs_P6HE.{u} ε ≤ C1 → capCollarCs_P6HE.{u} ε ≤ C2 →
      ∀ (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        ‖x.val‖ ≤ StandardCap.transitionEnd + 10 →
        ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2 ((R.static b).window x),
          W.capTubeHasNeckChart ε := by
  obtain ⟨Rcap, mcap, εcap, hCs, hεcap, hR, hev⟩ := capCollarCs_spec_P6HE.{u} hε hε'
  exact ⟨Rcap, mcap, εcap, hCs, hεcap, hR,
    fun R hcan hacc hrad hord C1 C2 h1 h2 b x hx =>
      hev (R.static b) (hcan b) hacc hrad hord C1 C2 h1 h2 x hx⟩

end GC.LongTime.Ch11
