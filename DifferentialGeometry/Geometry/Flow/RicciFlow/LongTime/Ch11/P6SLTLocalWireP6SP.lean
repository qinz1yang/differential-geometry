import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalProdP6SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceDichotomyLateCg_P6LS3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HctrlNoJ10P6JA

/-!
# slice / hctrl 接同一局部合同（O-CH11-SLTPROD G2，后缀 `_P6SP`；J10GEN3 缺口表 4(i)）

J10GEN3 缺口表 4(i)：slice `hqRR`——`hsliceR_lateHI_core_P6S3` 把 `qcan` 喂单切片
`slice_dichotomy_late_Cg_window_P6LS3`；其非 CWP 分支
`slice_scalar_bound_of_not_capWindowPoint_window_pinch_P6LS3`（P6LS3:41）经 P6WB:515 SLT 窗口核吃
**全局** `K.EventSlabsDerivative Ctime qd` / `DerivativeBoundBefore Ctime qd v`（`qd ≤ q`；
`qd = qcan ≤ Cg·R` = J10 型阈值）。本文件：
* `RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_local_P6SP`
  （PROVISIONAL[`hWBloc`]）：P6LS3:41 孪生。P6WB:515 换 SLTLOCAL `hWBloc`（同一 binder 形，WBADAPT 可付）；
  `qd` 退出（阈值 = `q` 本身，slice 处 `q := Cg·Rn`）；前 slab 槽 = **与 anchor `hslabsLoc` 同一局部合同**
  （slice 帧 `t := v`、`y := w`，guard `(v − v')·max(q, R(v, z)) ≤ c`）；同 slab 槽 = U 形 `q` 阈值导数。
* `ObservedHistory.sliceSlabsLoc_of_hgood_stay_P6SP`（PROVED ⇐ slice 帧 `hstaySl`）：slice 前 slab 槽 ⇐
  **同一 producer 核** `slabDeriv_prefix_of_hgood_stay_P6SP`（G1：hgood 时间分量 + 距离形 stay），`Cg·R ≤ q`。
* `RetainedCoreHistory.slice_scalar_bound_local_of_hgood_P6SP`（PROVISIONAL[`hWBloc`, `hstaySl`]）：
  组合——slice 孪生的前 slab 槽由上条付清（hgood 单实例 + slice 帧 stay + 窗口两行）。
* `ObservedHistory.exists_hctrl_lateHI_noJ10_prod_P6SP`（PROVISIONAL[`hWBloc`, `hstayLoc`] + J10GEN2A
  hctrl 自带输入）：J10GEN2A `exists_hctrl_lateHI_noJ10_P6JA`（已无 `hqR′`）的 `hanchor0` 槽由 G1 anchor
  consumer `hanchor0_eventSlab_prod_P6SP` 付（hctrl 在 anchor 之后）。hctrl 自身 survival 槽
  `hslab` / `hderG`（`qcan` 阈值，全局形）原样保留。
birth 比较（缺口表 4(ii)：`qcan ≤ Cbirth·scale` 对 T₀ 之后全部 records）**不做**。**不声称 J10 已去。**
生成器 `build-logs/scratch/O-CH11-SLTPROD/gen/gen2.py` / `gen2b.py`（P6LS3:41 陈述 sha256 `c9f11faf…`、
J10GEN2A hctrl 陈述 sha256 `5e74261c…`、SLTLOCAL `hWBloc` 块 sha256 `bcc5186f…`、G1 `hstayLoc` 块 sha256
`6be42e3e…` assert 切出）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **slice 非 CWP 分支局部孪生（`_P6SP`，PROVISIONAL[`hWBloc`]）**：P6LS3:41 逐字，P6WB:515 换 `hWBloc`
（∃ 常数多 `c`），`∀ qd, qd ≤ q → EventSlabsDerivative Ctime qd → DerivativeBoundBefore Ctime qd v` 换成
前 slab 局部槽（guard `(v − v')·max(q, R(v, z)) ≤ c`，与 anchor `hslabsLoc` 同形）+ 同 slab U 形 `q` 阈值槽。 -/
theorem RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_local_P6SP
    (hWBloc : ∀ (ε : ℝ), ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0)
      (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi → ∀ (A : ℝ), 0 < A →
      ∀ (Cq θ : ℝ), 0 < θ →
      ∃ Q Λ Dcap Rrad ζ₀ Rad Bw c : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
      Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧ 0 < c ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
          (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
        Λ ≤ G.flow.scalar t y * t →
        ∀ {p : CutoffParameters} (T₀ : ℝ), T₀ ≤ t - Bw / G.flow.scalar t y →
        ∀ (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
          GeometricCutoffRecord H.toHistory i p),
        (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
        Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
        ∀ (U : Set (H.stage (Fin.last H.eventCount)).Carrier),
        (∀ w ∈ riemannianBallOf (G.flow.base.metric t) y (Rad / Real.sqrt (G.flow.scalar t y)),
          w ∈ U) →
        (∀ x ∈ U, q < G.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        (∀ j : Fin H.eventCount,
          ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), t - Bw / G.flow.scalar t y ≤ v →
          (t - v) * max q (G.flow.scalar t z) ≤ c →
          q < (H.toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * (H.toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential G.flow v x w| ≤
              Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
                Real.sqrt ((G.flow.base.metric v).inner x w w)) →
        (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
          (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (t - Bw / G.flow.scalar t y)) phi) →
        Perelman.PhiAlmostNonnegative G.flow
          (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici (t - Bw / G.flow.scalar t y)) phi →
        (∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t →
          t - Bw / G.flow.scalar t y ≤ T →
          let B := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
          let tm : Icc (0 : ℝ) B.horizon := ⟨T, H.horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) →
        Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
        (¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
          (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
          (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            t - H.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
          G.flow.scalar t z ≤ Q * G.flow.scalar t y)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad Bw c : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧ 0 < c ∧
    ∀ (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow
        (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi) →
    ∀ (v : ℝ), K.time j.castSucc < v → v < K.time j.succ →
    ∀ (w : (K.stage j.castSucc).Carrier) (q ρ : ℝ),
      T₀ ≤ v - Bw / (K.toHistory.event j).incoming.flow.scalar v w →
      0 < q → q ≤ Cq * (K.toHistory.event j).incoming.flow.scalar v w →
      Λ ≤ (K.toHistory.event j).incoming.flow.scalar v w →
      Λ ≤ (K.toHistory.event j).incoming.flow.scalar v w * v →
      Λ ≤ ρ * Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w) →
    ∀ U : Set (K.stage j.castSucc).Carrier,
      (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
        (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)), x ∈ U) →
      (∀ x ∈ U, q < (K.toHistory.event j).incoming.flow.scalar v x →
        ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
          ε C1 C2 x, W.capTubeHasNeckChart ε) →
      (∀ i : Fin (K.prefixAt j.castSucc).eventCount,
        ∀ (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
        ∀ z ∈ U, ∀ Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
          (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z,
        ∀ v' ∈ Ioo ((K.prefixAt j.castSucc).time i.castSucc)
          ((K.prefixAt j.castSucc).time i.succ),
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        (v - v') * max q ((K.toHistory.event j).incoming.flow.scalar v z) ≤ c →
        q < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
          (Btr.point i.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun s => ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar s
          (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v') v'| ≤
          Ctime * ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
            (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2) →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        |derivWithin (fun s => (K.toHistory.event j).incoming.flow.scalar s x) (Iic v') v'| ≤
          Ctime * (K.toHistory.event j).incoming.flow.scalar v' x ^ 2) →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        ∀ ξ : TangentSpace ThreeModel x,
          |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
            Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
              Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
              Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
        K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
        ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
              (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) →
      (¬ ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ j.castSucc)
        (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl w)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          v - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (A / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
        (K.toHistory.event j).incoming.flow.scalar v z ≤
          Q * (K.toHistory.event j).incoming.flow.scalar v w := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, c, hQ, hΛ, hD, hDR, hζ₀, hBw, hc, hmain⟩ :=
    hWBloc ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi A hA Cq (1 / 2) (by norm_num)
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, c, hQ, hΛ, hD, hDR, hζ₀, hBw, hc, ?_⟩
  intro K j p T₀ records hcan hR hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ U hU hW
    hslabs hder hgrad hnc hnot
  have hncB := K.tested_noncollapse_eventPrefix_P6M j (κ := κ) (ρ := ρ)
    (a := v - Bw / (K.toHistory.event j).incoming.flow.scalar v w) (t := v) U hnc
    (K.prefixAt_time_last _)
  exact hmain (K.prefixAt j.castSucc) (K.prefixAt_time_last _) (K.toHistory.event j).incoming
    (K.event_initial j) hv1 hv2 w q ρ hq hqC hΛR hΛt
    T₀ hT₀ (fun i hT => K.geometricCutoffRecordOfPrefix j.castSucc
      (records (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT))
    (fun i hT b => hcan (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT b) hR hord hacc U hU
    hW hslabs hder hgrad
    (fun i v' hv' ξ => hpinch (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) v'
      ⟨hv'.1, hT₀.trans hv'.2⟩ ξ)
    (fun v' hv' ξ => hpinch j v' ⟨hv'.1, hT₀.trans hv'.2⟩ ξ) hncB hΛρ
    (by
      rintro ⟨i, hT, hl, Btr, b, x, h1, h2, h3⟩
      exact hnot ⟨Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i, hT,
        Fin.le_def.mpr (Fin.le_def.mp hl), K.backwardPointTraceOfPrefix j.castSucc Btr, b, x, h1,
        h2, h3⟩)

namespace ObservedHistory

/-- **slice 前 slab 局部槽 ⇐ 同一 producer 核（`_P6SP`，PROVED ⇐ 显式 binder `hstaySl`）**：slice 帧
（slab `j` 内切片时刻 `v`、基点 `w`、`U`、阈值 `q ≥ Cg·R`）的前 slab 局部槽
（guard `(v − v')·max(q, R(v, z)) ≤ c`）⇐ hgood 单实例时间分量 + slice 帧距离形 stay `hstaySl` +
窗口两行（`aSeed ≤ v − max c 1/R`、`σ − L²/R ≤ v − max c 1/R`），逐点调 G1
`slabDeriv_prefix_of_hgood_stay_P6SP`——与 anchor `hslabsLoc` 同一核。 -/
theorem sliceSlabsLoc_of_hgood_stay_P6SP {eps C1' C2' : ℝ} {Ctime : ℝ≥0} {Cg R L q Bw c : ℝ}
    (hCg : 1 ≤ Cg) (hR : 0 < R) (hqC : Cg * R ≤ q)
    (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (y : (K.toHistory.stageAt σ).Carrier)
    (hgood : ∀ (v'' : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v'') (hvs : v'' ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v'' : ℝ) →
      ∀ z : (K.toHistory.stageAt v'').Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v'') v'')
            (seedTrace.point (K.toHistory.activeStage v'') (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v'') v'') z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime v'' z)
    {v : ℝ} (hv1 : K.time j.castSucc < v) (hvσ : v ≤ (σ : ℝ))
    (w : (K.stage j.castSucc).Carrier) (U : Set (K.stage j.castSucc).Carrier)
    (hwinSl : (aSeed : ℝ) ≤ v - max c 1 / R) (hLSl : (σ : ℝ) - L ^ 2 / R ≤ v - max c 1 / R)
    (hstaySl : ∀ i : Fin (K.prefixAt j.castSucc).eventCount,
      ∀ (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ U, ∀ Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
        (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z,
      ∀ v' ∈ Ioo ((K.prefixAt j.castSucc).time i.castSucc)
        ((K.prefixAt j.castSucc).time i.succ),
      v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
      (v - v') * max q ((K.toHistory.event j).incoming.flow.scalar v z) ≤ c →
      q < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      ∀ (v'' : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v'') (hvs : v'' ≤ σ),
        (v'' : ℝ) = v' →
      ∀ x : (K.toHistory.stageAt v'').Carrier, HEq x (Btr.point i.castSucc hf (Fin.le_last _)) →
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v'') v'')
            (seedTrace.point (K.toHistory.activeStage v'') (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) x ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R)) :
    ∀ i : Fin (K.prefixAt j.castSucc).eventCount,
      ∀ (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ U, ∀ Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
        (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z,
      ∀ v' ∈ Ioo ((K.prefixAt j.castSucc).time i.castSucc)
        ((K.prefixAt j.castSucc).time i.succ),
      v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
      (v - v') * max q ((K.toHistory.event j).incoming.flow.scalar v z) ≤ c →
      q < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun s => ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar s
        (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v') v'| ≤
        Ctime * ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
          (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2 := by
  intro i first hf z hz Btr v' hv' hBv hcv hq'
  have hlast : (K.prefixAt j.castSucc).time i.succ ≤ K.time j.castSucc :=
    ((K.prefixAt j.castSucc).time_strictMono.monotone (Fin.le_last _)).trans_eq
      (K.prefixAt_time_last _)
  have hvt : v' < v := hv'.2.trans_le (hlast.trans hv1.le)
  have htv0 : 0 ≤ v - v' := by linarith
  have hRq : R ≤ q := by nlinarith
  have hguard : (v - v') * R ≤ max c 1 := by
    have h3 := mul_le_mul_of_nonneg_left (hRq.trans
      (le_max_left q ((K.toHistory.event j).incoming.flow.scalar v z))) htv0
    linarith [le_max_left c 1]
  have hTv : v - v' ≤ max c 1 / R := by
    rw [le_div_iff₀ hR]
    exact hguard
  have hv0 : 0 ≤ v' := ((K.prefixAt j.castSucc).toHistory.time_nonneg _).trans hv'.1.le
  have hvH : v' ≤ K.toHistory.horizon := (hvt.le.trans hvσ).trans σ.2.2
  let v'' : Icc (0 : ℝ) K.toHistory.horizon := ⟨v', hv0, hvH⟩
  have hav : aSeed ≤ v'' := by
    change (aSeed : ℝ) ≤ v'
    linarith
  have hvs : v'' ≤ σ := by
    change v' ≤ (σ : ℝ)
    linarith
  have hLv : (σ : ℝ) - L ^ 2 / R ≤ (v'' : ℝ) := by
    change (σ : ℝ) - L ^ 2 / R ≤ v'
    linarith
  exact slabDeriv_prefix_of_hgood_stay_P6SP K j.castSucc haT hsT has seedTrace y R L hgood i
    (Btr.point i.castSucc hf (Fin.le_last _)) v'' hav hvs hv'.1 hv'.2 hLv
    (hstaySl i first hf z hz Btr v' hv' hBv hcv hq' v'' hav hvs rfl) (lt_of_le_of_lt hqC hq')

end ObservedHistory

/-- **slice 组合（`_P6SP`，PROVISIONAL[`hWBloc`, `hstaySl`]）**：slice 局部孪生的前 slab 槽由
`sliceSlabsLoc_of_hgood_stay_P6SP`（同一 producer 核）付清；剩 hgood 单实例 + slice 帧 stay + 窗口两行 +
`Cg·R ≤ q`（slice 处 `q := Cg·Rn`）。无 `qd` / `EventSlabsDerivative` / `DerivativeBoundBefore` 前提。 -/
theorem RetainedCoreHistory.slice_scalar_bound_local_of_hgood_P6SP
    (hWBloc : ∀ (ε : ℝ), ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0)
      (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi → ∀ (A : ℝ), 0 < A →
      ∀ (Cq θ : ℝ), 0 < θ →
      ∃ Q Λ Dcap Rrad ζ₀ Rad Bw c : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
      Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧ 0 < c ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
          (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
        Λ ≤ G.flow.scalar t y * t →
        ∀ {p : CutoffParameters} (T₀ : ℝ), T₀ ≤ t - Bw / G.flow.scalar t y →
        ∀ (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
          GeometricCutoffRecord H.toHistory i p),
        (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
        Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
        ∀ (U : Set (H.stage (Fin.last H.eventCount)).Carrier),
        (∀ w ∈ riemannianBallOf (G.flow.base.metric t) y (Rad / Real.sqrt (G.flow.scalar t y)),
          w ∈ U) →
        (∀ x ∈ U, q < G.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        (∀ j : Fin H.eventCount,
          ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), t - Bw / G.flow.scalar t y ≤ v →
          (t - v) * max q (G.flow.scalar t z) ≤ c →
          q < (H.toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * (H.toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential G.flow v x w| ≤
              Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
                Real.sqrt ((G.flow.base.metric v).inner x w w)) →
        (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
          (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (t - Bw / G.flow.scalar t y)) phi) →
        Perelman.PhiAlmostNonnegative G.flow
          (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici (t - Bw / G.flow.scalar t y)) phi →
        (∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t →
          t - Bw / G.flow.scalar t y ≤ T →
          let B := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
          let tm : Icc (0 : ℝ) B.horizon := ⟨T, H.horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) →
        Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
        (¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
          (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
          (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            t - H.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
          G.flow.scalar t z ≤ Q * G.flow.scalar t y)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad Bw c : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧ 0 < c ∧
    ∀ (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow
        (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi) →
    ∀ (v : ℝ), K.time j.castSucc < v → v < K.time j.succ →
    ∀ (w : (K.stage j.castSucc).Carrier) (q ρ : ℝ),
      T₀ ≤ v - Bw / (K.toHistory.event j).incoming.flow.scalar v w →
      0 < q → q ≤ Cq * (K.toHistory.event j).incoming.flow.scalar v w →
      Λ ≤ (K.toHistory.event j).incoming.flow.scalar v w →
      Λ ≤ (K.toHistory.event j).incoming.flow.scalar v w * v →
      Λ ≤ ρ * Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w) →
    ∀ U : Set (K.stage j.castSucc).Carrier,
      (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
        (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)), x ∈ U) →
      (∀ x ∈ U, q < (K.toHistory.event j).incoming.flow.scalar v x →
        ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
          ε C1 C2 x, W.capTubeHasNeckChart ε) →
      ∀ (eps C1' C2' Cg R L : ℝ), 1 ≤ Cg → 0 < R → Cg * R ≤ q →
      ∀ (Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon) (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
        (has : aSeed ≤ σ) (pT : (K.toHistory.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
          (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
        (y : (K.toHistory.stageAt σ).Carrier),
      (∀ (v'' : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v'') (hvs : v'' ≤ σ),
        (σ : ℝ) - L ^ 2 / R ≤ (v'' : ℝ) →
        ∀ z : (K.toHistory.stageAt v'').Carrier,
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v'') v'')
              (seedTrace.point (K.toHistory.activeStage v'') (K.toHistory.activeStage_mono hav)
                (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
            riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
                (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                  (K.toHistory.activeStage_mono hsT)) y +
              ENNReal.ofReal (L / Real.sqrt R) →
          Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v'') v'') z →
          K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime v'' z) →
      v ≤ (σ : ℝ) → (aSeed : ℝ) ≤ v - max c 1 / R → (σ : ℝ) - L ^ 2 / R ≤ v - max c 1 / R →
      (∀ i : Fin (K.prefixAt j.castSucc).eventCount,
        ∀ (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
        ∀ z ∈ U, ∀ Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
          (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z,
        ∀ v' ∈ Ioo ((K.prefixAt j.castSucc).time i.castSucc)
          ((K.prefixAt j.castSucc).time i.succ),
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        (v - v') * max q ((K.toHistory.event j).incoming.flow.scalar v z) ≤ c →
        q < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
          (Btr.point i.castSucc hf (Fin.le_last _)) →
        ∀ (v'' : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v'') (hvs : v'' ≤ σ),
          (v'' : ℝ) = v' →
        ∀ x : (K.toHistory.stageAt v'').Carrier, HEq x (Btr.point i.castSucc hf (Fin.le_last _)) →
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v'') v'')
              (seedTrace.point (K.toHistory.activeStage v'') (K.toHistory.activeStage_mono hav)
                (K.toHistory.activeStage_mono (hvs.trans hsT))) x ≤
            riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
                (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                  (K.toHistory.activeStage_mono hsT)) y +
              ENNReal.ofReal (L / Real.sqrt R)) →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        |derivWithin (fun s => (K.toHistory.event j).incoming.flow.scalar s x) (Iic v') v'| ≤
          Ctime * (K.toHistory.event j).incoming.flow.scalar v' x ^ 2) →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        ∀ ξ : TangentSpace ThreeModel x,
          |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
            Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
              Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
              Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
        K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
        ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
              (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) →
      (¬ ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ j.castSucc)
        (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl w)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          v - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (A / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
        (K.toHistory.event j).incoming.flow.scalar v z ≤
          Q * (K.toHistory.event j).incoming.flow.scalar v w := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, c, hQ, hΛ, hD, hDR, hζ₀, hBw, hc, hmain⟩ :=
    RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_local_P6SP hWBloc hεle κ
      C1 C2 hκ Ctime Cgrad hphi A hA Cq
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, c, hQ, hΛ, hD, hDR, hζ₀, hBw, hc, ?_⟩
  intro K j p T₀ records hcan hR hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ U hU hW
    eps C1' C2' Cg R L hCg hR0 hqsel Tn aSeed σ haT hsT has pT seedTrace y hgood hvσ hwinSl hLSl
    hstaySl hder hgrad hnc hnot
  exact hmain K j T₀ records hcan hR hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ U hU
    hW (ObservedHistory.sliceSlabsLoc_of_hgood_stay_P6SP hCg hR0 hqsel K j haT hsT has seedTrace y
      hgood hv1 hvσ w U hwinSl hLSl hstaySl) hder hgrad hnc hnot

namespace ObservedHistory

/-- **hctrl 接 anchor 局部合同（`_P6SP`，PROVISIONAL[`hWBloc`, `hstayLoc`] + J10GEN2A hctrl 自带输入）**：
J10GEN2A `exists_hctrl_lateHI_noJ10_P6JA`（已无 `hqR′`）逐字，`hanchor0` 槽删去、由 G1 anchor consumer
`hanchor0_eventSlab_prod_P6SP` 付（hctrl 在 anchor 之后）；anchor 侧多出的输入（`hWBloc`、`hεcone`、`hCg`、
`hRlt`、κ 侧 `hvolK`、`hwin`、`hdistW`、`hstayLoc`）追加为 binder，hgood 常数统一为 hctrl 的
`epsG C1G C2G CtG`。注意：hctrl 自身的 survival 槽 `hslab` / `hderG`（`qcan` 阈值，全局形）原样保留——
其局部化（survival 核 `hsurvive_noJ10_P6JC` 孪生，anchor 之后可用 first-exit）不在本块。 -/
theorem exists_hctrl_lateHI_noJ10_prod_P6SP
    (hWBloc : ∀ (ε : ℝ), ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0)
      (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi → ∀ (A : ℝ), 0 < A →
      ∀ (Cq θ : ℝ), 0 < θ →
      ∃ Q Λ Dcap Rrad ζ₀ Rad Bw c : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
      Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧ 0 < c ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
          (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
        Λ ≤ G.flow.scalar t y * t →
        ∀ {p : CutoffParameters} (T₀ : ℝ), T₀ ≤ t - Bw / G.flow.scalar t y →
        ∀ (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
          GeometricCutoffRecord H.toHistory i p),
        (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
        Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
        ∀ (U : Set (H.stage (Fin.last H.eventCount)).Carrier),
        (∀ w ∈ riemannianBallOf (G.flow.base.metric t) y (Rad / Real.sqrt (G.flow.scalar t y)),
          w ∈ U) →
        (∀ x ∈ U, q < G.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        (∀ j : Fin H.eventCount,
          ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), t - Bw / G.flow.scalar t y ≤ v →
          (t - v) * max q (G.flow.scalar t z) ≤ c →
          q < (H.toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * (H.toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential G.flow v x w| ≤
              Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
                Real.sqrt ((G.flow.base.metric v).inner x w w)) →
        (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
          (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (t - Bw / G.flow.scalar t y)) phi) →
        Perelman.PhiAlmostNonnegative G.flow
          (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici (t - Bw / G.flow.scalar t y)) phi →
        (∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t →
          t - Bw / G.flow.scalar t y ≤ T →
          let B := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
          let tm : Icc (0 : ℝ) B.horizon := ⟨T, H.horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
          ∀ z ∈ U, ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) →
        Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
        (¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
          (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
          (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            t - H.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
          G.flow.scalar t z ≤ Q * G.flow.scalar t y)
    {Ctime : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {D θcap qcan T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters} {δb : ℕ → ℝ}
    {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (pF n))
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x,
      InFixedHamiltonIveyRegion (((K n).prefixAt (j n).castSucc).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (j n).castSucc).initialMetric 0) x)
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
      T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
      (pF n).delta (((K n).prefixAt (j n).castSucc).time i.succ) ≤ δb n)
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i hi b,
      ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((records n i hi).static b).neck.scale)
    (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
    (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
        Perelman.PhiAlmostNonnegative
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow
          (Ico (((K n).prefixAt (j n).castSucc).time i.castSucc)
            (((K n).prefixAt (j n).castSucc).time i.succ) ∩ Ici (T₀ n)) phi) ∧
      Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
        (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ) ∩ Ici (T₀ n)) phi)
    (hslab : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (qcan n)
      (Fin.last ((K n).prefixAt (j n).castSucc).eventCount))
    (hderG : ∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore (2 * Ctime)
      (2 * qcan n) (t n))
    (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
      (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
      (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
        t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
          θcap n * (((records n i hi).static b).neck.scale)⁻¹)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
      t n) atTop atTop)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hR : ∀ n, 0 < R n) (hRlim : Tendsto R atTop atTop)
    (Hs : ℕ → ObservedHistory.{u})
    (hHs : Hs = fun n => ((K n).eventPrefix (j n) (t n) (hjt n) (htj n)).toHistory)
    (ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (hts' : HEq ts (fun n => ((K n).prefixAt (j n).castSucc).extendAtTime
      ((K n).prefixAt_time_last _) ((K n).toHistory.event (j n)).incoming
      ((K n).event_initial (j n)) (hjt n) (htj n)))
    (ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier) (hys : ∀ n, HEq (ys n) (yG n))
    {epsG C1G C2G Cg : ℝ} {CtG : ℝ≥0}
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl epsG C1G C2G CtG v z)
    (TnE aE : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haTE : ∀ n, aE n ≤ TnE n)
    (hsTE : ∀ n, ts n ≤ TnE n) (hasE : ∀ n, aE n ≤ ts n)
    (pTE : ∀ n, ((Hs n).stageAt (TnE n)).Carrier)
    (seedE : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aE n))
      ((Hs n).activeStage (TnE n)) ((Hs n).activeStage_mono (haTE n)) (pTE n))
    (haa : ∀ n, (aSeed n : ℝ) ≤ aE n)
    (hseedC : ∀ n (v : Icc (0 : ℝ) (Hs n).horizon) (v' : Icc (0 : ℝ) (Kh n).horizon),
      (v : ℝ) = v' →
      ∀ (h1 : (Hs n).activeStage (aE n) ≤ (Hs n).activeStage v)
        (h2 : (Hs n).activeStage v ≤ (Hs n).activeStage (TnE n))
        (h1' : (Kh n).activeStage (aSeed n) ≤ (Kh n).activeStage v')
        (h2' : (Kh n).activeStage v' ≤ (Kh n).activeStage (Tn n)),
        HEq ((seedE n).point ((Hs n).activeStage v) h1 h2)
          ((seedTrace n).point ((Kh n).activeStage v') h1' h2'))
    {rX : ℝ}
    (hC2G : 0 ≤ C2G)
    (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Hs n) (TnE n) (pTE n) rX)
    (hclock : ∀ n, (aE n : ℝ) = (TnE n : ℝ) - rX ^ 2)
    (a₀X : ℕ → ℝ)
    (ha₀X : ∀ n, 0 ≤ a₀X n)
    (hpinX : ∀ n (τ : Icc (0 : ℝ) (Hs n).horizon) (x : ((Hs n).stageAt τ).Carrier),
      InFixedHamiltonIveyRegion ((Hs n).stageMetric ((Hs n).activeStage τ) τ) (a₀X n + τ) x)
    (hRa : ∀ n, 1 ≤ R n * aE n)
    (qX : ℕ → CutoffParameters)
    (T₀X : ℕ → ℝ)
    (hT₀X : ∀ n, T₀X n ≤ aE n)
    (recordsX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (qX n))
    (hOldX : ∀ n (e : Fin (Hs n).eventCount), T₀X n ≤ (Hs n).time e.succ →
      ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore)
    (hcanX : ∀ n (e : Fin (Hs n).eventCount) (he : T₀X n ≤ (Hs n).time e.succ) b,
      ((recordsX n e he).static b).hasCanonicalWindow)
    (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (qX n).modelRadius)
    (haccX : ∀ n : ℕ, (qX n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hmX : ∀ n, 2 ≤ (qX n).modelOrder)
    (hsepX : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ (e : Fin (Hs n).eventCount)
      (he : T₀X n ≤ (Hs n).time e.succ) b, (aE n : ℝ) < (Hs n).time e.succ →
        M * R n < ((recordsX n e he).static b).neck.scale)
    (hfinX : ∀ n, riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
        ((seedE n).point ((Hs n).activeStage (ts n)) ((Hs n).activeStage_mono (hasE n))
          ((Hs n).activeStage_mono (hsTE n))) (ys n) ≠ ⊤)
    (hεcone : epsG ≤ coneAccuracy) (hCg : 2 ≤ Cg)
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    {κd : ℝ} (hκd : 0 < κd)
    (hvolK : ∀ D L B : ℝ, 0 < D → 0 < L → 0 < B → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - B / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        (Kh n).isParabolicallyRmControlledBall v
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
          (ϱ / Real.sqrt (R n)) →
        ENNReal.ofReal (κd * ϱ ^ 3) ≤
          Geometry.Collapse.ballVolume
            (scaleMetric (R n) (hR n) ((Kh n).stageMetric ((Kh n).activeStage v) v))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ϱ)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hstayLoc : ∀ Rad B c : ℝ, ∀ᶠ n in atTop,
      ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
      ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
      ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
        (((K n).prefixAt (j n).castSucc).time i.succ),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      (t n - v) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤ c →
      Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      ∀ (v' : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v') (hvs : v' ≤ σ n),
        (v' : ℝ) = v →
      ∀ x : ((Kh n).stageAt v').Carrier, HEq x (Btr.point i.castSucc hf (Fin.le_last _)) →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v') v')
            ((seedTrace n).point ((Kh n).activeStage v')
              ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n))
                ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ᶠ n in atTop,
      (Kh n).isParabolicallyRmControlledBall (σ n) (y n) (r / Real.sqrt (R n)) :=
  exists_hctrl_lateHI_noJ10_P6JA hphi hjt htj recordsF hHI hcan hδF hqcan hpar hscale hbirthA hθcap
    hpinch hslab hderG hnot hT₀ hRt
    (hanchor0_eventSlab_prod_P6SP hWBloc hεcone hC2G hphi hjt htj hcan hpar hθcap hpinch hnot hT₀
      hRt Kh hKh σ hσ y hyG R hR hRn hRlt hκd hvolK Tn aSeed haT hsT has pT seedTrace L hL hCg
      hgood hwin hdistW hstayLoc)
    Kh hKh σ y R hσ hyG hRn hR hRlim Hs hHs ts hts' ys hys Tn aSeed haT hsT has pT seedTrace L hL
    hgood TnE aE haTE hsTE hasE pTE seedE haa hseedC hC2G hrX hsmall hclock a₀X ha₀X hpinX hRa qX
    T₀X hT₀X recordsX hOldX hcanX hDmX haccX hmX hsepX hfinX

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
