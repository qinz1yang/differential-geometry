import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceDichotomyLate_P6L3

/-!
# late 单切片二分：阈值系数 `Cg` + `[T₀, ∞)` 窗口 pinching（S-CH11-P6CG G2，后缀 `_P6LS3`）

P6ANCH3 HANDOVER ①②：
* `slice_scalar_bound_of_not_capWindowPoint_window_pinch_P6LS3`：
  `slice_scalar_bound_of_not_capWindowPoint_P6L2`（SLT 窗口版 `…_terminal_window_P6WB` 的 K 层单切片
  包装）副本，pinching 前提 `K.EventSlabsPinched phi` 换成 `[T₀, ∞)` 窗口形：逐 event
  `PhiAlmostNonnegative (K.event i).incoming.flow
  (Ico (time i.castSucc) (time i.succ) ∩ Ici T₀) phi`。
  SLT 窗口版本身只要 `Ici (v − Bw/R(v, w))` 窗口（`T₀ ≤ v − Bw/R` ⇒ `Ici T₀` 窗口更大），故只改前提
  到 SLT 的转接（`hv'.1` → `⟨hv'.1, hT₀.trans hv'.2⟩`）。
* `slice_dichotomy_late_Cg_window_P6LS3`：`slice_dichotomy_late_P6L3` 副本：新参数
  `(Cg) (hCg : 0 < Cg)`（紧接 `Cgrad`，在常数 `∃ Cbirth … Bw …` **之前**，因 Rad / Bw / Λ 依赖
  `Cq := Cg`）；写死的 `4` 换 `Cg`（`qcan ≤ Cg·Rn`、U 侧 witness / 梯度阈值 `Cg·Rn`、
  `slice_scalar_bound … Cg`）；pinching 同上窗口形。`capWindow_branch_late_P6L3`（CWP 分支，阈值无关）
  原样复用。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **非 CWP 分支（单切片，K 层，late records，窗口 pinching，`_window_pinch_P6LS3`）**：
`slice_scalar_bound_of_not_capWindowPoint_P6L2` 的副本，pinching 前提 `K.EventSlabsPinched phi` 换成
`[T₀, ∞)` 窗口形（逐 event `PhiAlmostNonnegative … (Ico … ∩ Ici T₀) phi`）；SLT 窗口版 `Ici (v − Bw/R)`
窗口 ⇐ `T₀ ≤ v − Bw/R` 单调。 -/
theorem RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_pinch_P6LS3
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
      ∀ qd : ℝ, qd ≤ q → K.EventSlabsDerivative Ctime qd j.castSucc →
      (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qd v →
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
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB
      hεle κ C1 C2 hκ Ctime Cgrad hphi A hA Cq (1 / 2) (by norm_num)
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, hDR, hζ₀, hBw, ?_⟩
  intro K j p T₀ records hcan hR hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ U hU hW
    qd hqd hslabK hderG hgrad hnc hnot
  have hslabP := K.eventSlabsDerivative_prefixAt j.castSucc (fun i hi => hslabK i hi)
  have hncB := K.tested_noncollapse_eventPrefix_P6M j (κ := κ) (ρ := ρ)
    (a := v - Bw / (K.toHistory.event j).incoming.flow.scalar v w) (t := v) U hnc
    (K.prefixAt_time_last _)
  exact hmain (K.prefixAt j.castSucc) (K.prefixAt_time_last _) (K.toHistory.event j).incoming
    (K.event_initial j) hv1 hv2 w q ρ hq hqC hΛR hΛt
    T₀ hT₀ (fun i hT => K.geometricCutoffRecordOfPrefix j.castSucc
      (records (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT))
    (fun i hT b => hcan (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT b) hR hord hacc U hU
    hW
    (fun i first hf z _ Btr v' hv' _ hRv' =>
      hslabP i (Fin.castSucc_lt_last i) _ v' hv' (lt_of_le_of_lt hqd hRv'))
    (fun x _ v' hv' _ hRv' => hderG x v' hv' (lt_of_le_of_lt hqd hRv')) hgrad
    (fun i v' hv' ξ => hpinch (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) v'
      ⟨hv'.1, hT₀.trans hv'.2⟩ ξ)
    (fun v' hv' ξ => hpinch j v' ⟨hv'.1, hT₀.trans hv'.2⟩ ξ) hncB hΛρ
    (by
      rintro ⟨i, hT, hl, Btr, b, x, h1, h2, h3⟩
      exact hnot ⟨Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i, hT,
        Fin.le_def.mpr (Fin.le_def.mp hl), K.backwardPointTraceOfPrefix j.castSucc Btr, b, x, h1,
        h2, h3⟩)

/-- **切片二分（单切片，near-trace + late records，`_P6L3`）**：`slice_dichotomy_late_P6L3` 的 late 版
（CWP 分支 = `capWindow_branch_late_P6L3`）。event slab `j` 内部切片 `v`、stage 变量 `k = j.castSucc`（`subst`；
供序列层取 `k := activeStage v`）、基点 `z`（trace 点）与 seed 点 `sk`（`HEq sk sj`）、`d(sk, z) ≤ d1`；
U 侧前提（Good 区 `d(sj, w) ≤ d1 + Dd/√Rn`、`Rn ≤ R(w)` 的每个 `w` 上：witness / 梯度 / 区域 κ，阈值 `4Rn`）
+ slab 导数数据（同时喂 SLT 的 `hslabs`/`hder` 与 G2p）+ CWP 分支数据 ⇒ Kdata `hslice` 的二分体
（`CWP := K.CapWindowPoint records j.castSucc · v Dcap (1/2)`）。 -/
theorem RetainedCoreHistory.slice_dichotomy_late_Cg_window_P6LS3
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
    ∀ (Rn ρ : ℝ), 0 < Rn → qcan ≤ Cg * Rn → Λ ≤ Rn → Λ ≤ Rn * v → Λ ≤ ρ * Real.sqrt Rn →
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
                (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))) →
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
    RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_pinch_P6LS3 hεle κ C1 C2 hκ
      Ctime Cgrad hphi (2 * Dd * Real.sqrt A + 1) hAB Cg
  have hDpos : 0 < Dcap := StandardCap.transitionEnd_pos.trans hD
  have hDD₂ : Dcap < Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) := by
    have : 0 ≤ 2 * Dd * Lc * Real.sqrt (2 * A) := by positivity
    linarith
  obtain ⟨Rr, -, m₀, -, ζ₁, δ₀, hζ₁, hδ₀, hcap⟩ :=
    hCWP Dcap (Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1)) η₃ hDpos hDD₂ hη₃
  refine ⟨Q, Dcap, Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1), by linarith, le_rfl, Λ, Rad,
    Bw, max Rr Rrad, min ζ₀ ζ₁, δ₀, max m₀ 2, hΛ, hBw, lt_min hζ₀ hζ₁, hδ₀, ?_⟩
  intro K p T₀ records hcan hRad hord hacc hpinch pF recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow
    hbirth j hslab v hv1 hv2 hder Rn ρ hRn hqR hΛRn hΛv hΛρ hT₀ k hk z sk sj hs d1 hzd zj hzj hU
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
    obtain ⟨h1, h4, h5⟩ := hU w hw hzw hRw
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
      hT₀w (lt_of_lt_of_le hq0 hqR) (mul_le_mul_of_nonneg_left hRw2 hCg.le) (hΛRn.trans hRw)
      (hΛv.trans (mul_le_mul_of_nonneg_right hRw hv0))
      (hΛρ.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRw) hρ0.le)) _ (fun _ h => h) h1
      qcan hqR hslab hder h4 h5 hncw x hx
  · intro w _ hcw
    exact hcap K records hcan ((le_max_left _ _).trans hRad) ((le_max_left _ _).trans hord)
      (hacc.trans (min_le_right _ _)) recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow hbirth
      j hslab v hv1 hv2 hder w hcw

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
