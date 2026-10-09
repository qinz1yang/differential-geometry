import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceDichotomyLateCg_P6LS3

/-!
# K-SW：自身尺度短窗的 slice dichotomy（O-CH11-KSW G1，后缀 `_C11KS`）

SHALLOW 设计（`docs/geometrization/chapter8/design-C11-shallow-20261007.md` §3 I4）把 K-SW 标 BLOCKED，
理由是"需要 Rm 版 strong maximum principle + metric-cone 刚性，树内未见"。本车道 G0 核查结论：
* **锥刚性已在树**：`solution_cone_terminal_exclusion`（`Perelman/CanonicalNeighborhood/
  ConeTerminalExclusion.lean:60`）——cone chart 上的 concurrent field `Z`（`∇Z = Id`）满足
  `Ric(Z, Z) = 0`（终端时刻）且 `sec ≥ 0` 给 `Ric(Z, Z) ≥ 0`（`[a, b]` 上），终端一阶极值 + Ricci 演化
  ⇒ `2R ≤ 0`，与非平坦矛盾；**任意短窗 `a < b`** 即可，不需要 Hamilton SMP。经
  `rescaled_end_cone_exclusion`（`Compactness/ConeExclusion.lean:172`）接入 SLT 链（Perelman I.12.1
  Step 2 形）。SNAP root64 审计：standard axioms only。
* **"深窗 `Bw`" 是 F5 伪影**：SLT 窗口链里 `hQa : Q (t − a) → ∞` 只以 `eventually_ge_atTop θ` 被消费，
  `θ` 是 base 尺度 buffer 的存在量（可收缩）；锥点层 `Q₂ = qk · Q`、`qk → ∞` 自动变深。证据表见
  `build-logs/resume/state-O-CH11-KSW.md`。
本文件（无占位证明）：
* `ShortSLT_C11KS θ`（**binder / repair target X**）：SLT 窗口版主定理
  `exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB` 的陈述逐字，只把
  存在量 `Bw` 换成 CWP 年龄参数 `θ` 本身（窗口 `t − θ/R(t, y)`）。
* `slice_scalar_bound_of_not_capWindowPoint_short_C11KS`：LS3 非 CWP 包装的短窗副本（PROVED ⇐ X）。
* `KSW_C11KS θ₀`（**K-SW 合同**）：`slice_dichotomy_late_Cg_window_P6LS3` 的陈述逐字，`Bw` 换固定 `θ₀`
  （U 侧梯度 / 区域 κ 窗 `[v − θ₀/R(v, w), v]`，`T₀ ≤ v − θ₀/R_n`；`Cg` 参数照旧，覆盖 `Cg ∈ {4, 8}`）。
* `ksw_of_shortSLT_C11KS`（主定理，PROVISIONAL，binder = `ShortSLT_C11KS θ₀`，`0 < θ₀ ≤ 1/2`）：
  CWP 谓词取年龄 `θ₀`；CWP 分支 = `capWindow_branch_late_P6L3`（年龄 `θ₀ ≤ 1/2`）。
* `KSW_C11KS.mono`：`θ₀ ≤ θ₁` ⇒ `KSW θ₀ → KSW θ₁`（短窗版更强）。
* X 的机械替换件（PROVED）：`window_start_le_of_buffer_C11KS`、`tendsto_coneScale_window_C11KS`、
  `buffer_time_mono_C11KS`、`exists_buffer_le_C11KS`、`window_depth_eq_C11KS`。
非循环（D-19）：只 import LS3（SLT 窗口链 + CWP late 分支）；无 hscalU / hclosG / hclosC /
CanonicalLateCore / hspine。不声称闭合。
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

/-- **binder X（`_C11KS`）**：
`exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB` 的陈述逐字，
只把存在量窗口深度 `Bw` 换成 CWP 年龄参数 `θ`（树内版的 SL 层只要 `θ ≤ Bw`）。
repair target：base 层窗口链（TTC:110 / Cone:108 / TL2 / TP:97 / TC×4 / SLT core）的短窗副本，
`hQa : Q (t − a) → ∞` 换 `θ ≤ Q (t − a)` + buffer `min` 收缩；锥点层原样复用。 -/
def ShortSLT_C11KS (θ : ℝ) : Prop :=
  ∀ {ε : ℝ}, ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ},
    Perelman.AdmissiblePinchingFunction phi → ∀ (A : ℝ), 0 < A → ∀ Cq : ℝ,
    ∃ Q Λ Dcap Rrad ζ₀ Rad : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧
    ∀ (H : RetainedCoreHistory.{u})
      (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount))
      {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
      Λ ≤ G.flow.scalar t y * t →
      ∀ {p : CutoffParameters} (T₀ : ℝ), T₀ ≤ t - θ / G.flow.scalar t y →
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
        ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), t - θ / G.flow.scalar t y ≤ v →
        q < (H.toHistory.event j).incoming.flow.scalar v
          (B.point j.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
          (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
          Ctime * (H.toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
      (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - θ / G.flow.scalar t y ≤ v →
        q < G.flow.scalar v x →
        |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2) →
      (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - θ / G.flow.scalar t y ≤ v →
        q < G.flow.scalar v x →
        ∀ w : TangentSpace ThreeModel x,
          |scalarDifferential G.flow v x w| ≤
            Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
              Real.sqrt ((G.flow.base.metric v).inner x w w)) →
      (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (t - θ / G.flow.scalar t y)) phi) →
      Perelman.PhiAlmostNonnegative G.flow
        (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici (t - θ / G.flow.scalar t y)) phi →
      (∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t →
        t - θ / G.flow.scalar t y ≤ T →
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
        G.flow.scalar t z ≤ Q * G.flow.scalar t y

/-- **非 CWP 分支（短窗，`_C11KS`）**：`slice_scalar_bound_of_not_capWindowPoint_window_pinch_P6LS3`
的副本，SLT 换 binder `ShortSLT_C11KS θ`：窗口 `v − θ/R(v, w)`、`hnot` 的 CWP 年龄 `θ`。 -/
theorem RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_short_C11KS
    {θ : ℝ} (hS : ShortSLT_C11KS.{u} θ)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧
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
      T₀ ≤ v - θ / (K.toHistory.event j).incoming.flow.scalar v w →
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
        v - θ / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        ∀ ξ : TangentSpace ThreeModel x,
          |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
            Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
              Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
              Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        v - θ / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
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
          v - K.time i.succ ≤ θ * (((records i hT).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (A / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
        (K.toHistory.event j).incoming.flow.scalar v z ≤
          Q * (K.toHistory.event j).incoming.flow.scalar v w := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, hD, hDR, hζ₀, hmain⟩ :=
    hS hεle κ C1 C2 hκ Ctime Cgrad hphi A hA Cq
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, hD, hDR, hζ₀, ?_⟩
  intro K j p T₀ records hcan hR hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ U hU hW
    qd hqd hslabK hderG hgrad hnc hnot
  have hslabP := K.eventSlabsDerivative_prefixAt j.castSucc (fun i hi => hslabK i hi)
  have hncB := K.tested_noncollapse_eventPrefix_P6M j (κ := κ) (ρ := ρ)
    (a := v - θ / (K.toHistory.event j).incoming.flow.scalar v w) (t := v) U hnc
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

/-- **K-SW 合同（`_C11KS`）**：`slice_dichotomy_late_Cg_window_P6LS3` 的陈述逐字，只把存在量 `Bw`
换成固定 `θ₀`：U 侧梯度 / 区域 κ 只在坏点自身尺度短窗 `[v − θ₀/R(v, w), v]` 上要求，
`T₀ ≤ v − θ₀/R_n`。常数 `QB Dcap D₂ Λ Rad …` 只依赖 `(A, Dd)` 与开头参数（含 `Cg`）。 -/
def KSW_C11KS (θ₀ : ℝ) : Prop :=
  ∀ {ε : ℝ}, ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0) (Cg : ℝ),
    0 < Cg → ∀ {phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction phi → ∀ {η₃ Lc : ℝ},
    0 < η₃ → 0 < Lc →
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
    Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
    ∃ (Λ Rad Rmin ζmin δ₀ : ℝ) (m₀ : ℕ), 1 ≤ Λ ∧ 0 < ζmin ∧ 0 < δ₀ ∧
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
      T₀ ≤ v - θ₀ / Rn →
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
          v - θ₀ / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
          Cg * Rn < (K.toHistory.event j).incoming.flow.scalar v' x →
          ∀ ξ : TangentSpace ThreeModel x,
            |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
              Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
                Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
                Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) ∧
        (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
          v - θ₀ / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
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
                (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)

/-- **K-SW ⇐ X（`_C11KS`，PROVISIONAL：binder `ShortSLT_C11KS θ₀`）**：
`slice_dichotomy_late_Cg_window_P6LS3` 的证明副本；非 CWP 分支 =
`slice_scalar_bound_of_not_capWindowPoint_short_C11KS`，CWP 谓词取年龄 `θ₀`，
CWP 分支 = `capWindow_branch_late_P6L3`（`θ₀ ≤ 1/2` ⇒ 年龄 `≤ 1/2`）。 -/
theorem ksw_of_shortSLT_C11KS {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2)
    (hS : ShortSLT_C11KS.{u} θ₀) : KSW_C11KS.{u} θ₀ := by
  intro ε hεle κ C1 C2 hκ Ctime Cgrad Cg hCg phi hphi η₃ Lc hη₃ hLc
  obtain ⟨Cbirth, hCbirth, hCWP⟩ := RetainedCoreHistory.capWindow_branch_late_P6L3.{u} Ctime
  refine ⟨Cbirth, hCbirth, fun A Dd hA hDd => ?_⟩
  have hAB : 0 < 2 * Dd * Real.sqrt A + 1 := by positivity
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, hD, -, hζ₀, hmain⟩ :=
    RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_short_C11KS hS hεle κ C1 C2 hκ
      Ctime Cgrad hphi (2 * Dd * Real.sqrt A + 1) hAB Cg
  have hDpos : 0 < Dcap := StandardCap.transitionEnd_pos.trans hD
  have hDD₂ : Dcap < Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) := by
    have : 0 ≤ 2 * Dd * Lc * Real.sqrt (2 * A) := by positivity
    linarith
  obtain ⟨Rr, -, m₀, -, ζ₁, δ₀, hζ₁, hδ₀, hcap⟩ :=
    hCWP Dcap (Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1)) η₃ hDpos hDD₂ hη₃
  refine ⟨Q, Dcap, Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1), by linarith, le_rfl, Λ, Rad,
    max Rr Rrad, min ζ₀ ζ₁, δ₀, max m₀ 2, hΛ, lt_min hζ₀ hζ₁, hδ₀, ?_⟩
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
        v - K.time i.succ ≤ θ₀ * (((records i hT).static b).neck.scale)⁻¹, ?_, ?_⟩
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
    have hT₀w : T₀ ≤ v - θ₀ / (K.toHistory.event j).incoming.flow.scalar v w :=
      hT₀.trans (by linarith [div_le_div_of_nonneg_left hθ₀.le hRn hRw2])
    exact hmain K j T₀ records hcan ((le_max_right _ _).trans hRad) ((le_max_right _ _).trans hord)
      (hacc.trans (min_le_left _ _)) hpinch v hv1 hv2 w (Cg * Rn) ρ
      hT₀w (lt_of_lt_of_le hq0 hqR) (mul_le_mul_of_nonneg_left hRw2 hCg.le) (hΛRn.trans hRw)
      (hΛv.trans (mul_le_mul_of_nonneg_right hRw hv0))
      (hΛρ.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRw) hρ0.le)) _ (fun _ h => h) h1
      qcan hqR hslab hder h4 h5 hncw x hx
  · intro w _ hcw
    obtain ⟨i, hT, hl, B, b, x, h1, h2, h3⟩ := hcw
    exact hcap K records hcan ((le_max_left _ _).trans hRad) ((le_max_left _ _).trans hord)
      (hacc.trans (min_le_right _ _)) recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow hbirth
      j hslab v hv1 hv2 hder w ⟨i, hT, hl, B, b, x, h1, h2, h3.trans
        (mul_le_mul_of_nonneg_right hθ₀2
          (inv_nonneg.mpr ((records i hT).static b).neck.scale_pos.le))⟩

/-- **短窗单调（`_C11KS`）**：`θ₀ ≤ θ₁` ⇒ `KSW_C11KS θ₀ → KSW_C11KS θ₁`（窗越短，前提越弱、定理越强）。
故取 `θ₀ := θ_* = 1/(2 max(Ctime, 1))`（SHALLOW §2.4）即覆盖更长的窗。 -/
theorem KSW_C11KS.mono {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (h : KSW_C11KS.{u} θ₀) : KSW_C11KS.{u} θ₁ := by
  intro ε hεle κ C1 C2 hκ Ctime Cgrad Cg hCg phi hphi η₃ Lc hη₃ hLc
  obtain ⟨Cbirth, hCbirth, hP⟩ := h hεle κ C1 C2 hκ Ctime Cgrad Cg hCg hphi hη₃ hLc
  refine ⟨Cbirth, hCbirth, fun A Dd hA hDd => ?_⟩
  obtain ⟨QB, Dcap, D₂, hQB, hD₂, Λ, Rad, Rmin, ζmin, δ₀, m₀, hΛ, hζ, hδ₀, hmain⟩ :=
    hP A Dd hA hDd
  refine ⟨QB, Dcap, D₂, hQB, hD₂, Λ, Rad, Rmin, ζmin, δ₀, m₀, hΛ, hζ, hδ₀, ?_⟩
  intro K p T₀ records hcan hRad hord hacc hpinch pF recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow
    hbirth j hslab v hv1 hv2 hder Rn ρ hRn hqR hΛRn hΛv hΛρ hT₀ k hk z sk sj hs d1 hzd zj hzj hU
  have hRdiv := div_le_div_of_nonneg_right hθ hRn.le
  refine hmain K T₀ records hcan hRad hord hacc hpinch recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow
    hbirth j hslab v hv1 hv2 hder Rn ρ hRn hqR hΛRn hΛv hΛρ (hT₀.trans (by linarith)) k hk z sk sj
    hs d1 hzd zj hzj ?_
  intro w hw hzw hRw
  obtain ⟨h1, h2, h3⟩ := hU w hw hzw hRw
  have hRw0 : 0 < (K.toHistory.event j).incoming.flow.scalar v w := hRn.trans_le hRw
  have hdiv := div_le_div_of_nonneg_right hθ hRw0.le
  exact ⟨h1, fun x hx v' hv' hle => h2 x hx v' hv' (by linarith),
    fun τ hτ => h3 τ (by linarith)⟩

/-- **X 替换件（a，`_C11KS`）**：`θ ≤ θa ≤ Q (s − a)` ⇒ `a ≤ s − θ/Q`。短窗副本里代替
`hQa.eventually_ge_atTop θ` + `hwn`（`TracedTerminalCompactnessWindow_P6WA.lean:198–203` 型）。 -/
theorem window_start_le_of_buffer_C11KS {Q s a θ θa : ℝ} (hQ : 0 < Q) (hθ : θ ≤ θa)
    (ha : θa ≤ Q * (s - a)) : a ≤ s - θ / Q := by
  have h1 : θ / Q ≤ s - a := (div_le_iff₀ hQ).mpr (by rw [mul_comm]; linarith)
  linarith

/-- **X 替换件（b，`_C11KS`）**：base 层固定窗 `θa ≤ Q (t − a)` + 锥点比 `qk → ∞` ⇒ 锥点层
`(qk · Q)(t − a) → ∞`。代替 `BoundedCurvatureAtDistanceTracedConeWindow_P6WA.lean:275–277` 的 `hQc₂`
（那里 `Q₂ m = qk m * Q (f (k m))`、`hqklim : qk → ∞`，:230 / :244），锥点层文件原样复用。 -/
theorem tendsto_coneScale_window_C11KS {qk Qb d : ℕ → ℝ} {θa : ℝ} (hθa : 0 < θa)
    (hqk : Tendsto qk atTop atTop) (hQd : ∀ m, θa ≤ Qb m * d m) :
    Tendsto (fun m => qk m * Qb m * d m) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (hqk.atTop_mul_const hθa)
  filter_upwards [hqk.eventually_ge_atTop 0] with m hm
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hQd m) hm

/-- **X 替换件（c，`_C11KS`）**：buffer 起点对 `θ` 单调：`tf ≤ s − θ/Q`、`θ′ ≤ θ` ⇒ `tf ≤ s − θ′/Q`。 -/
theorem buffer_time_mono_C11KS {tf s θ θ' Q : ℝ} (hQ : 0 < Q) (hθ' : θ' ≤ θ)
    (h : tf ≤ s - θ / Q) : tf ≤ s - θ' / Q := by
  have := div_le_div_of_nonneg_right hθ' hQ.le
  linarith

/-- **X 替换件（d，`_C11KS`）**：对 `θ` 向下封闭的 buffer 性质，存在量 `θ` 可收缩到 `≤ θa`。 -/
theorem exists_buffer_le_C11KS {P : ℝ → Prop} (hP : ∀ θ θ', 0 < θ' → θ' ≤ θ → P θ → P θ')
    (h : ∃ θ, 0 < θ ∧ P θ) {θa : ℝ} (hθa : 0 < θa) : ∃ θ, 0 < θ ∧ θ ≤ θa ∧ P θ := by
  obtain ⟨θ, hθ, hPθ⟩ := h
  exact ⟨min θ θa, lt_min hθ hθa, min_le_right _ _,
    hP θ _ (lt_min hθ hθa) (min_le_left _ _) hPθ⟩

/-- **X 替换件（e，`_C11KS`）**：SLT 反证里窗口起点 `a = t − θ/R` 的深度恒为 `θ`（代替
`BoundedCurvatureAtDistanceSliceTerminalWindow_P6WB.lean:397` 的 `hQa`，`Bw n = n + 1 + θ` 不再需要）。 -/
theorem window_depth_eq_C11KS {R t θ : ℝ} (hR : 0 < R) : R * (t - (t - θ / R)) = θ := by
  rw [sub_sub_cancel]
  field_simp

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
