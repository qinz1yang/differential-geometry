import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6WBAdaptStarP6WA2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceDichotomyLateCg_P6LS3

/-!
# 切片二分的局部化孪生：去 `hqR`，SLT 支 Dt 进 U 侧（O-CH11-SLICEDICH G1，后缀 `_P6SD`）

J10 残余（DEPTH4C / DEPTH3 更正）：DEPTH3 hbcadC producer 吃 `hslabK`（全局 Dt，阈值 `Q n`）+
`hqR : max(n+1, Q n) ≤ R n`，源头 = `slice_dichotomy_late_Cg_window_P6LS3`（P6LS3:130）的 `hslab` / `hder`
（阈值 `qcan`）+ `qcan ≤ Cg·Rn`。G0 逐行清单（state-O-CH11-SLICEDICH）：
* D1（P6LS3:102/:112–113）SLT 支前 slab trace Dt ⇒ guarded ShortSLT 缩到 guard 深度（L1）+ U 侧合取；
* D2（:114）SLT 支同 slab Dt ⇒ U 侧合取（与梯度同形，producer = hgood 时间分量 + hclosC）；
* D3（:266）CWP 支 Dt（阈值 `qcan`，约束只有 `qcan ≤ Cbirth·scale`）⇒ 原样保留，与 `Rn` 脱钩；
* D4（:157）`qcan ≤ Cg·Rn` ⇒ 删。
本文件：
* L1 `slice_scalar_bound_of_not_capWindowPoint_window_local_star_P6SD`（PROVED，无 binder）：
  SLTPROD G2 slice 孪生（P6SP:50）去 `hWBloc`、guard 固定 `c⋆`，由
  `hWBlocStar_of_shortSLT_guarded_P6WA2` 付。
* L2 `slice_dichotomy_late_Cg_window_local_P6SD`（PROVED，无 binder）：P6LS3:130 孪生，无 `qcan ≤ Cg·Rn`，
  U 侧多 D2 / D1 两合取（阈值 `Cg·Rn`）。
* consumer `example`：原前提（全局 Dt + `qcan ≤ Cg·Rn`）⇒ D1 / D2 合取（孪生前提不强于原定理）。
不声称 J10 已去：D1 合取的 producer 需要 U 点短深度跨 surgery 的 stay（G2 的 `hstaySlC`）。
生成器 `build-logs/scratch/O-CH11-SLICEDICH/gen/gen1.py`（从 tracked P6SP / P6LS3 逐字切片 + assert 替换）。
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

/-- **L1 单切片 SLT star 孪生（`_P6SD`，PROVED，无 binder）**：SLTPROD G2
`slice_scalar_bound_of_not_capWindowPoint_window_local_P6SP`（P6SP:50）的陈述去掉 `hWBloc` binder，
`∃ … c` 去掉、前 slab guard 右端固定为 `c⋆ = 1/(2·max(Ctime, 1))`；由 WBADAPT G3
`hWBlocStar_of_shortSLT_guarded_P6WA2`（PROVED，guarded ShortSLT，`θ = Bw = 1/2`）支付。
D1（前 slab trace Dt）只在 guard 深度 `c⋆/max(q, R(v, z))` 内要；D2（同 slab Dt）为 U 形 `q` 阈值槽。 -/
theorem RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_local_star_P6SD
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad Bw : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧
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
        (v - v') * max q ((K.toHistory.event j).incoming.flow.scalar v z) ≤
          1 / (2 * max (Ctime : ℝ) 1) →
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
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, hDR, hζ₀, hBw, hmain⟩ :=
    hWBlocStar_of_shortSLT_guarded_P6WA2.{u} ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi A hA Cq
      (1 / 2) (by norm_num)
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, hDR, hζ₀, hBw, ?_⟩
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

/-- **L2 切片二分局部孪生（`_P6SD`，PROVED，无 binder）**：`slice_dichotomy_late_Cg_window_P6LS3`
（P6LS3:130）逐字，改动三处：
1. 删 `qcan ≤ Cg * Rn`（hqR）：原证明只在 :259（`0 < q`）与 :262（`qd ≤ q`，把 `qcan` 阈值全局 Dt 降到
   `q = Cg·Rn`）用它；现 `0 < q` ⇐ `mul_pos hCg hRn`，SLT 支 Dt 直接在阈值 `q` 上要。
2. 非 CWP 分支换 L1 star 孪生（guarded ShortSLT）；SLT 支的 Dt 从全局 `hslab` / `hder` 移进 U 侧合取（与
   witness / 梯度 / 区域 κ 同位置、同阈值 `Cg·Rn`）：D2 同 slab Dt（`Rad` 球 × 窗口）、D1 前 slab trace Dt
   （guard `(v − v')·max(Cg·Rn, R(v, z)) ≤ c⋆`，`c⋆ = 1/(2·max(Ctime, 1))`）。
3. `hslab` / `hder`（阈值 `qcan`，全局形）只喂 CWP 分支 `capWindow_branch_late_P6L3`，后者只约束
   `qcan ≤ Cbirth·scale`——与 `Rn` 脱钩（cap 输入，(α′) / HNOT 前缀 Dt 形）。 -/
theorem RetainedCoreHistory.slice_dichotomy_late_Cg_window_local_P6SD
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) (Cg : ℝ)
    (hCg : 0 < Cg) {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
    Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
    ∃ (Λ Rad Bw Rmin ζmin δ₀ : ℝ) (m₀ : ℕ), 1 ≤ Λ ∧ 0 < Bw ∧ 0 < ζmin ∧ 0 < δ₀ ∧
    ∀ (K : RetainedCoreHistory.{u}) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rmin ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζmin →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow
        (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi) →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord K.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        pF.delta (K.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (K.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (K.initialMetric 0) x) →
      (∀ i hT b, qcan ≤ Cbirth * ((records i hT).static b).neck.scale ∧
        1 ≤ a₀ * ((records i hT).static b).neck.scale) →
    ∀ (j : Fin K.eventCount), K.EventSlabsDerivative Ctime qcan j.castSucc →
    ∀ v : ℝ, K.time j.castSucc < v → v < K.time j.succ →
      (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan v →
    ∀ (Rn ρ : ℝ), 0 < Rn → Λ ≤ Rn → Λ ≤ Rn * v → Λ ≤ ρ * Real.sqrt Rn →
      T₀ ≤ v - Bw / Rn →
    ∀ (k : Fin (K.eventCount + 1)), k = j.castSucc →
    ∀ (z sk : (K.toHistory.stage k).Carrier) (sj : (K.stage j.castSucc).Carrier), HEq sk sj →
    ∀ d1 : ENNReal, riemannianEDistOf (K.toHistory.stageMetric k v) sk z ≤ d1 →
    ∀ zj : (K.stage j.castSucc).Carrier, HEq z zj →
    (∀ w : (K.stage j.castSucc).Carrier,
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) sj w ≤
        d1 + ENNReal.ofReal (Dd / Real.sqrt Rn) →
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) zj w <
        ENNReal.ofReal (Dd / Real.sqrt Rn) →
      Rn ≤ (K.toHistory.event j).incoming.flow.scalar v w →
        (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
              (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          Cg * Rn < (K.toHistory.event j).incoming.flow.scalar v x →
          ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
            ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
        (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
              (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          ∀ v' ∈ Ioo (K.time j.castSucc) v,
          v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
          Cg * Rn < (K.toHistory.event j).incoming.flow.scalar v' x →
          ∀ ξ : TangentSpace ThreeModel x,
            |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
              Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
                Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
                Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) ∧
        (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
          v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
          K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
          ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
                (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
                (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
                (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) ∧
        (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
              (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          ∀ v' ∈ Ioo (K.time j.castSucc) v,
          v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
          Cg * Rn < (K.toHistory.event j).incoming.flow.scalar v' x →
          |derivWithin (fun s => (K.toHistory.event j).incoming.flow.scalar s x) (Iic v') v'| ≤
            Ctime * (K.toHistory.event j).incoming.flow.scalar v' x ^ 2) ∧
        (∀ i : Fin (K.prefixAt j.castSucc).eventCount,
          ∀ (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
          ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
              (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          ∀ Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
            (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z,
          ∀ v' ∈ Ioo ((K.prefixAt j.castSucc).time i.castSucc)
            ((K.prefixAt j.castSucc).time i.succ),
          v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
          (v - v') * max (Cg * Rn) ((K.toHistory.event j).incoming.flow.scalar v z) ≤
            1 / (2 * max (Ctime : ℝ) 1) →
          Cg * Rn < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
            (Btr.point i.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun s =>
              ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v') v'| ≤
            Ctime * ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2)) →
    ∃ CWP : (K.toHistory.stage k).Carrier → Prop,
      (∀ w, riemannianEDistOf (K.toHistory.stageMetric k v)
          z w <
          ENNReal.ofReal (Dd / Real.sqrt Rn) → ¬ CWP w →
        Rn ≤ metricScalarAt (K.toHistory.stageMetric k v) w → ∀ x,
        riemannianEDistOf (K.toHistory.stageMetric k v) w x <
          ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
            Real.sqrt (metricScalarAt (K.toHistory.stageMetric k v) w)) →
        metricScalarAt (K.toHistory.stageMetric k v) x ≤
          QB * metricScalarAt (K.toHistory.stageMetric k v) w) ∧
      (∀ w, riemannianEDistOf (K.toHistory.stageMetric k v)
          z w <
          ENNReal.ofReal (Dd / Real.sqrt Rn) → CWP w →
        ∃ (Ξ : standardCapWindow D₂ → (K.toHistory.stage k).Carrier)
          (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
          Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
          ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
            τw ∈ Icc (0 : ℝ) (1 / 2) ∧
            ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
              metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                  (K.toHistory.stageMetric k v)) Ξ hΞ)
                ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  obtain ⟨Cbirth, hCbirth, hCWP⟩ := RetainedCoreHistory.capWindow_branch_late_P6L3.{u} Ctime
  refine ⟨Cbirth, hCbirth, fun A Dd hA hDd => ?_⟩
  have hAB : 0 < 2 * Dd * Real.sqrt A + 1 := by positivity
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, -, hζ₀, hBw, hmain⟩ :=
    RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_local_star_P6SD hεle κ C1 C2
      hκ Ctime Cgrad hphi (2 * Dd * Real.sqrt A + 1) hAB Cg
  have hDpos : 0 < Dcap := StandardCap.transitionEnd_pos.trans hD
  have hDD₂ : Dcap < Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) := by
    have : 0 ≤ 2 * Dd * Lc * Real.sqrt (2 * A) := by positivity
    linarith
  obtain ⟨Rr, -, m₀, -, ζ₁, δ₀, hζ₁, hδ₀, hcap⟩ :=
    hCWP Dcap (Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1)) η₃ hDpos hDD₂ hη₃
  refine ⟨Q, Dcap, Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1), by linarith, le_rfl, Λ, Rad,
    Bw, max Rr Rrad, min ζ₀ ζ₁, δ₀, max m₀ 2, hΛ, hBw, lt_min hζ₀ hζ₁, hδ₀, ?_⟩
  intro K p T₀ records hcan hRad hord hacc hpinch pF recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow
    hbirth j hslab v hv1 hv2 hder Rn ρ hRn hΛRn hΛv hΛρ hT₀ k hk z sk sj hs d1 hzd zj hzj hU
  subst hk
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq hzj
  have hv0 : 0 ≤ v := (K.toHistory.time_nonneg _).trans hv1.le
  refine ⟨fun w => ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ j.castSucc)
      (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl w)
      (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        v - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹, ?_, ?_⟩
  · intro w hzw hncw hRw x hx
    rw [ObservedHistory.stageMetric_castSucc_apply] at hzd hzw hRw hx ⊢
    have hw : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) sk w ≤
        d1 + ENNReal.ofReal (Dd / Real.sqrt Rn) :=
      (riemannianEDistOf_triangle _ _ _ _).trans (add_le_add hzd hzw.le)
    obtain ⟨h1, h4, h5, h6, h7⟩ := hU w hw hzw hRw
    have hRw2 : Rn ≤ (K.toHistory.event j).incoming.flow.scalar v w := hRw
    have hρ0 : 0 < ρ := by
      by_contra hneg
      have : ρ * Real.sqrt Rn ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (Real.sqrt_nonneg _)
      linarith
    have hT₀w : T₀ ≤ v - Bw / (K.toHistory.event j).incoming.flow.scalar v w :=
      hT₀.trans (by linarith [div_le_div_of_nonneg_left hBw.le hRn hRw2])
    exact hmain K j T₀ records hcan ((le_max_right _ _).trans hRad) ((le_max_right _ _).trans hord)
      (hacc.trans (min_le_left _ _)) hpinch v hv1 hv2 w (Cg * Rn) ρ
      hT₀w (mul_pos hCg hRn) (mul_le_mul_of_nonneg_left hRw2 hCg.le) (hΛRn.trans hRw)
      (hΛv.trans (mul_le_mul_of_nonneg_right hRw hv0))
      (hΛρ.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRw) hρ0.le)) _ (fun _ h => h) h1
      h7 h6 h4 h5 hncw x hx
  · intro w _ hcw
    exact hcap K records hcan ((le_max_left _ _).trans hRad) ((le_max_left _ _).trans hord)
      (hacc.trans (min_le_right _ _)) recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow hbirth
      j hslab v hv1 hv2 hder w hcw

/-- **consumer（`_P6SD`）**：L2 孪生 ⇒ 原 `slice_dichotomy_late_Cg_window_P6LS3` 的单实例用法——原前提
（全局 `hslab` / `hder` 于 `qcan` + `qcan ≤ Cg·Rn`）给出 U 侧 D1 / D2 合取（`eventSlabsDerivative_prefixAt`
+ `qcan ≤ Cg·Rn < R`），故孪生的前提不强于原定理（健全性方向）。 -/
example {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    (Cg : ℝ) (hCg : 0 < Cg) {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {η₃ Lc : ℝ} (hη₃ : 0 < η₃) (hLc : 0 < Lc) (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    (qcan Rn v : ℝ) (hqR : qcan ≤ Cg * Rn)
    (hslab : K.EventSlabsDerivative Ctime qcan j.castSucc)
    (hder : (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan v)
    (w : (K.stage j.castSucc).Carrier) (Rad Bw : ℝ) :
    (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
      ∀ v' ∈ Ioo (K.time j.castSucc) v,
      v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
      Cg * Rn < (K.toHistory.event j).incoming.flow.scalar v' x →
      |derivWithin (fun s => (K.toHistory.event j).incoming.flow.scalar s x) (Iic v') v'| ≤
        Ctime * (K.toHistory.event j).incoming.flow.scalar v' x ^ 2) ∧
    (∀ i : Fin (K.prefixAt j.castSucc).eventCount,
      ∀ (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
      ∀ Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
        (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z,
      ∀ v' ∈ Ioo ((K.prefixAt j.castSucc).time i.castSucc)
        ((K.prefixAt j.castSucc).time i.succ),
      v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
      (v - v') * max (Cg * Rn) ((K.toHistory.event j).incoming.flow.scalar v z) ≤
        1 / (2 * max (Ctime : ℝ) 1) →
      Cg * Rn < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun s =>
          ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar s
            (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v') v'| ≤
        Ctime * ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
          (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2) ∧
    ∃ Cbirth : ℝ, 0 < Cbirth := by
  have hslabP := K.eventSlabsDerivative_prefixAt j.castSucc (fun i hi => hslab i hi)
  refine ⟨fun x _ v' hv' _ hR => hder x v' hv' (lt_of_le_of_lt hqR hR),
    fun i first hf z _ Btr v' hv' _ _ hR =>
      hslabP i (Fin.castSucc_lt_last i) _ v' hv' (lt_of_le_of_lt hqR hR), ?_⟩
  obtain ⟨Cbirth, hCbirth, -⟩ := RetainedCoreHistory.slice_dichotomy_late_Cg_window_local_P6SD.{u}
    hεle κ C1 C2 hκ Ctime Cgrad Cg hCg hphi hη₃ hLc
  exact ⟨Cbirth, hCbirth⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
