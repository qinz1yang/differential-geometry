import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallC11PB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWFixedWindowC11KS2

/-!
# picked-ball 合同 × 固定窗 K-SW（O-CH11-PICKBALL G3，后缀 `_C11PB`）

KSW2 已交 `shortSLT_C11KS2 : 0 < θ → ShortSLT_C11KS θ` 与
`ksw_C11KS2 : 0 < θ₀ → θ₀ ≤ 1/2 → KSW_C11KS θ₀`
（PROVED，root #66）。本文件把 G2 consumer 的 ShortSLT / K-SW binder 用它们付清，并把 SHALLOW T1 接线
`shallowSliceRC_of_ksw_short_C11KS` 的 U 侧前提 `hUVC`（每个合格 `w` 的 witness / 梯度 / κ 三元）换成
picked-ball 合同：
* `RetainedCoreHistory.capWindowPoint_or_scalar_bound_of_pickedBall_fixed_C11PB`：`0 < θ ≤ β` ⇒
  合同（`PickedBallWitnessGrad β Rad′ q` ∧ `PickedBallKappa β Rad′ ρ`）+ 全局数据 ⇒ CWP(θ) ∨ `R ≤ Q q`
  （无 ShortSLT binder）；
* `ksw_pickedBall_fixed_C11PB`：`0 < θ₀ ≤ 1/2`、`θ₀ ≤ β` ⇒ K-SW 二分（`hU` 换合同族；无 K-SW binder）；
* `ObservedHistory.shallowSliceRC_of_pickedBall_C11PB`：SHALLOW T1（`ShallowSliceRC_C11SH`）⇐
  `ksw_C11KS2` + KSW consumer 的其余前提逐字 + **selection `HgoodCg_C11SH Cg`**（witness 半：空间余量
  `Rad ≤ L/2`、时间域 `σ + σ₁/R ≥ max(aSeed, σ − L²/R)` 均 eventually，`pickedBallWitness_of_hgood_C11PB`）
  + 两族 binder：`hgradPB`（`PickedBallGrad_C11PB θ₀ Rad (Cg·R_n)`）与
  `hκPB`（`PickedBallKappa_C11PB θ₀ Rad ρV`），
  量词前缀与 `hUVC` 逐字（`∀ Rad σ₁ σ₂ φ Dw Dd T Kc`、traced 前件、`∀ᶠ n in map φ atTop`、合格 `w` 条件）。
状态：PROVISIONAL（binder = hgrad / hκ 两族；hpick 不进 T1 输入面）。非循环：只 import G1–G2 与 KSW2 G4
（→ KSW consumer、SHALLOW 骨架）；不经 hscalU / hclosG / hclosC / hUVC 生产者 / CanonicalLateCore / hspine。
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

/-- **ShortSLT 输入面 ⇐ 合同（固定窗，`_C11PB`，binder 已付）**：
`capWindowPoint_or_scalar_bound_of_pickedBall_C11PB` 的 `hS` 由 `shortSLT_C11KS2 hθ`（KSW2 G3）付清。 -/
theorem RetainedCoreHistory.capWindowPoint_or_scalar_bound_of_pickedBall_fixed_C11PB
    {θ β : ℝ} (hθ : 0 < θ) (hθβ : θ ≤ β)
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
    ∀ Rad' : ℝ, Rad ≤ Rad' →
      PickedBallWitnessGrad_C11PB β Rad' q ε C1 C2 Cgrad K j v w →
      PickedBallKappa_C11PB β Rad' ρ κ K j v w →
      ∀ qd : ℝ, qd ≤ q → K.EventSlabsDerivative Ctime qd j.castSucc →
      (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qd v →
      (∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ j.castSucc)
        (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl w)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          v - K.time i.succ ≤ θ * (((records i hT).static b).neck.scale)⁻¹) ∨
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (A / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
        (K.toHistory.event j).incoming.flow.scalar v z ≤
          Q * (K.toHistory.event j).incoming.flow.scalar v w :=
  RetainedCoreHistory.capWindowPoint_or_scalar_bound_of_pickedBall_C11PB (shortSLT_C11KS2 hθ) hθβ
    hεle κ C1 C2 hκ Ctime Cgrad hphi A hA Cq

/-- **K-SW 二分 ⇐ 合同（固定窗，`_C11PB`，binder 已付）**：`ksw_of_pickedBall_C11PB` 的 `hK` 由
`ksw_C11KS2 hθ₀ hθ₀2`（KSW2 G4）付清。 -/
theorem ksw_pickedBall_fixed_C11PB {θ₀ β : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2) (hθβ : θ₀ ≤ β) :
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
    ∀ Rad' : ℝ, Rad ≤ Rad' →
    (∀ w : (K.stage j.castSucc).Carrier,
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) sj w ≤
        d1 + ENNReal.ofReal (Dd / Real.sqrt Rn) →
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) zj w <
        ENNReal.ofReal (Dd / Real.sqrt Rn) →
      Rn ≤ (K.toHistory.event j).incoming.flow.scalar v w →
        PickedBallWitnessGrad_C11PB β Rad' (Cg * Rn) ε C1 C2 Cgrad K j v w ∧
          PickedBallKappa_C11PB β Rad' ρ κ K j v w) →
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
                (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) :=
  ksw_of_pickedBall_C11PB hθβ (ksw_C11KS2 hθ₀ hθ₀2)

/-- **SHALLOW T1 ⇐ picked-ball 合同（`_C11PB`，PROVISIONAL：binder `hgradPB` / `hκPB`）**：
`shallowSliceRC_of_ksw_short_C11KS` 的副本，`hK := ksw_C11KS2 hθ₀ hθ₀2`（PROVED），`Kh := (K n).toHistory`，
U 侧前提 `hUVC` 换成：witness 半 ⇐ `hgood`（`pickedBallWitness_of_hgood_C11PB`；空间余量 `Rad ≤ L/2`、
`aSeed ≤ v`（`hwin (−σ₁)`）、`σ − L²/R ≤ v`（`L ≥ max 1 (−σ₁)`）均由 `L → ∞` eventually 给出；`Rad < 0` 时球空），
梯度半 ⇐ `hgradPB`，κ ⇐ `hκPB`（量词前缀与 `hUVC` 逐字）。 -/
theorem ObservedHistory.shallowSliceRC_of_pickedBall_C11PB
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L ε C1 C2 Ctg)
    (hgradPB : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
        v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage
            (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w :
            ((K n).toHistory.stage j'.castSucc).Carrier),
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          PickedBallGrad_C11PB θ₀ Rad (Cg * R n) Cgrad (K n) j' v w)
    (hκPB : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
        v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage
            (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w :
            ((K n).toHistory.stage j'.castSucc).Carrier),
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          PickedBallKappa_C11PB θ₀ Rad (ρV n) κ (K n) j' v w) :
    ObservedHistory.ShallowSliceRC_C11SH η₃ Lc (fun n => (K n).toHistory) σ y R := by
  refine ObservedHistory.shallowSliceRC_of_ksw_short_C11KS (C1 := C1) (C2 := C2) (Cgrad := Cgrad)
    (ksw_C11KS2 hθ₀ hθ₀2) hεle hκ hphi hCg hη₃ hLc htj recordsF hHI hcanK hδF hacc hrad hord hscaleK
    hbirthA hpinchK0 hslabK
    (fun n => (K n).toHistory) rfl σ y R hσ hRpos hqR hT₀ Tn aSeed haT hsT has pT seedTrace L hL
    hwin ρV hρV hdistQC ?_
  intro Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
  have hσ₁ : 0 < -σ₁ := by linarith
  filter_upwards [hgradPB Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr,
    hκPB Rad σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr,
    hφ.tendsto_atTop (hL.eventually_ge_atTop (max (2 * Rad) (max 1 (-σ₁)))),
    hφ.tendsto_atTop (hwin (-σ₁) hσ₁)] with n hg hk hLn hwn
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hw hzw hRw
  refine ⟨?_, hg j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hw hzw hRw,
    hk j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hw hzw hRw⟩
  rcases le_or_gt 0 Rad with hRad0 | hRad0
  · have hRn := hRpos n
    have hL1 : 1 ≤ L n := (le_max_left _ _).trans ((le_max_right _ _).trans hLn)
    have hLσ : -σ₁ ≤ L n := (le_max_right _ _).trans ((le_max_right _ _).trans hLn)
    have hLR : 2 * Rad ≤ L n := (le_max_left _ _).trans hLn
    have hv0 : 0 ≤ v := ((K n).toHistory.time_nonneg _).trans hv1.le
    have hvh : v ≤ (K n).toHistory.horizon :=
      hv2.le.trans ((K n).toHistory.time_le_horizon_at _)
    have hσR : σ₁ / R n = -(-σ₁ / R n) := by rw [neg_div, neg_neg]
    have hσ2R : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    have hLsq : -σ₁ / R n ≤ L n ^ 2 / R n :=
      div_le_div_of_nonneg_right (by nlinarith) hRn.le
    exact pickedBallWitness_of_hgood_C11PB K hgood n j' ⟨v, hv0, hvh⟩ hv1 hv2
      (show (aSeed n : ℝ) ≤ v by linarith) (show v ≤ (σ n : ℝ) by linarith)
      (show (σ n : ℝ) - L n ^ 2 / R n ≤ v by linarith) h1 h2 w hRn hRw hRad0 (by linarith) hw
  · intro x hx _
    exfalso
    have hneg : Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hRad0.le (Real.sqrt_nonneg _)
    have hx' := lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hneg)
    rw [ENNReal.ofReal_zero] at hx'
    exact ENNReal.not_lt_zero hx'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
