import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ShallowT1FinalP6TF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFourthBcadP6AN4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFourthFinalHgoodP6AN4

/-!
# final 支 `hbcadC`（SHALLOW T0）⇐ T1 final 壳；ANCHOR4 final 全链 hbcadC 槽付清
（O-CH11-T1FINAL G2，后缀 `_P6TF`）

HBCADC final 支 BLOCKED 的 repair (R1) 落地：
* `ObservedHistory.hbcadC_final_of_pickedCenter_P6TF`（PROVISIONAL[`hPCF` + T1 late-K 组 + final 背景
  `hpinchF hderF` + `hdistQC`]）：结论 = SHALLOW T0 `ShallowBcadC_C11SH (K ·).toHistory σ y R`（=
  ANCHOR2/3/4 的 `hbcadC` binder 逐字）。证明 = ANCHOR4 G3 `shallowBcadC_of_sliceRC_any_P6AN4`（T1 ⇒ T0，无
  `σ < time last`，取其 `η₃ Lc`）∘ G1 consumer `shallowSliceRC_of_pickedCenter_final_P6TF`；`1 ≤ R n`
  ⇐ `hqR`。与 HBCADC event 版 `hbcadC_of_pickedCenter_P6BC` 的 binder 差：删 `j t htj hσ`，加
  `hfin G hG hpinchF hderF`，`hPC ↦ hPCF`（合同 final 形）。
* `hdistW_finalSlab_of_pickedCenter_P6TF`（PROVISIONAL）：ANCHOR4 G2b final 全链
  `hdistW_finalSlab_of_hgood_local_P6AN4` 的 `hbcadC` 槽由上式付清（`Kh` 消去为 `(K ·).toHistory`；T1 块插在结论前，共用链
  上的 `K σ y R κ ρnc hradii` 与 seed 组 `Tn aSeed … L hL hwin`；`hfin := htl.trans htK`，`G hG` 与链共用）。结论
  = `hdistW` 槽逐字（final 支）。

**final 全链剩余 binder 表**（hbcadC 消去后）：hseedTop（BLOCKED，ANCHOR4 G1）+ FINCOND 层 supplies（含
`hkappa / hseed / hwitC / records / schedule`）+ hgood（`HgoodCg_C11SH`）+ 导数背景 `hslab / hderG`（J10GEN）
+ P6DW K0 / HI + **T1 块**：late-K 组
`recordsFK hHIK hcanK hδFK haccK hradK hordK hscaleK hbirthAK hpinchK0 hslabK hqRK hT₀K`（整条 `K n`）、
final 背景 `hpinchFK`（FINCOND 同形，≠ J10GEN `hpinX`）/ `hderFK`（J10GEN 迁移类）、`hdistQC`（HDISTC，`L ↦ L/4`）、
`hPCF`（`PickedCenterNeighborhood_final_C11PT1` 族：event 分量 = PICKSEL 现有义务；final 分量 = 同一 StepOne / 窗口
seed / κ 三件的 final slab 版）。ceiling（CXJF2 / CXUT）不进 T1（`σ₂ < 0` ⇒ 切片 `< σ ≤ horizon`）。非循环：
`hbcadC_final_of_pickedCenter_P6TF` 的前提里没有 `hdistW` / `HU_` / `hanchor0` / `hgapJ` / `hclosG` /
`hscalU` / `CanonicalLateCore` / `hspine`；审计做传递依赖名字扫描（只对 T0 定理，全链定理本就依赖 AN4 链）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section T0

/-- **final 支 `hbcadC` ⇐ T1 final consumer（`_P6TF`，PROVISIONAL[`hPCF` + T1 late-K 组 +
`hpinchF hderF` + `hdistQC`]）**：结论 = SHALLOW T0 `ShallowBcadC_C11SH (K ·).toHistory σ y R`（= ANCHOR
`hbcadC` binder 逐字）。证明 = ANCHOR4 G3 `shallowBcadC_of_sliceRC_any_P6AN4`（T1 ⇒ T0，无 `σ < time last`）∘
`shallowSliceRC_of_pickedCenter_final_P6TF`；`1 ≤ R n` ⇐ `hqR`。σ 位置无关（final slab 或 event slab 都可，只要
`hfin`）。 -/
theorem ObservedHistory.hbcadC_final_of_pickedCenter_P6TF
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
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
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (K n).horizon)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
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
    (hPCF : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      PickedCenterNeighborhood_final_C11PT1 Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n) (ρV n) κ ε C1
        C2 Cgrad (K n) (G n) (σ n) (y n)) :
    ObservedHistory.ShallowBcadC_C11SH (fun n => (K n).toHistory) σ y R := by
  obtain ⟨η₃, _, Lc, hη₃, _, hLc, hT0⟩ := shallowBcadC_of_sliceRC_any_P6AN4.{u}
  refine hT0 K σ y R hRpos ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact h1.trans ((le_max_left _ _).trans (hqR n))
  · exact ObservedHistory.shallowSliceRC_of_pickedCenter_final_P6TF (C1 := C1) (C2 := C2)
      (Cgrad := Cgrad) hθ₀ hεle hκ hphi hCg hη₃ hLc hfin hG recordsF hHI hcanK hδF hacc hrad hord
      hscaleK hbirthA hpinchK0 hslabK hpinchF hderF σ y R hRpos hqR hT₀ Tn aSeed haT hsT has pT
      seedTrace L hL hwin ρV hρV hdistQC hPCF

end T0

section Anchor4Final

/-- **ANCHOR4 final 全链，`hbcadC` 槽付清（`_P6TF`，PROVISIONAL）**：`hdistW_finalSlab_of_hgood_local_P6AN4` 逐
字，`Kh` 消去为 `(K ·).toHistory`，`hbcadC` binder 删去，换成 T1 块（`K` 后缀 = 整条 `K n` 上的 late-K 组 +
`hpinchFK hderFK` + `hdistQC` + `hPCF`），插在结论 `∀ D T …` 之前（共用链上的 `G hG`、seed 组、`κ ρnc hradii`）。证明 =
AN4 全链喂 `hbcadC_final_of_pickedCenter_P6TF`（`hfin := htl.trans htK`，`R > 0` ⇐ `hRn` + `hqcan` +
`hqR`）。结论 = `hdistW` 槽逐字（final 支）。 -/
theorem hdistW_finalSlab_of_pickedCenter_P6TF :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      {ε : ℝ} → (hε : 0 < ε) → (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) →
      (hεN : ε ≤ crossingNeckAccuracy.{u}) →
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p pF : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      (recordsF : ∀ n i, GeometricCutoffRecord ((K n).prefixAt (Fin.last (K
        n).eventCount)).toHistory i (pF n)) →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      {a₀ : ℕ → ℝ} →
      (hHI : ∀ n x,
        InFixedHamiltonIveyRegion (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) (a₀
          n) x ∧
        -3 / a₀ n ≤ metricScalarAt (((K n).prefixAt (Fin.last (K n).eventCount)).initialMetric 0) x)
          →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hδF : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        (pF n).delta (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ≤ δb n) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀ n * ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hslab : ∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (qcan n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      (hderG : ∀ n, (G n).DerivativeBoundBefore (2 * Ctime)
        (2 * qcan n) (t n)) →
      (hqR : ∀ n, qcan n < (G n).flow.scalar (t n) (yG n)) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
        (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / (G n).flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hβ : 0 < β) →
      (hβ2 : β ≤ 1 / 2) →
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) →
          (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      {r₀ w : ℝ} → (hr₀ : 0 < r₀) → (hw : 0 < w) →
      (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel
              ((K n).toHistory.stageAt (σ n)).Carrier
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            (riemannianBallOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n)))) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (K n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) r'') →
      {C1s C2s Cs : ℝ} → {qs : ℕ → ℝ} → (hqs : ∀ n, qs n ≤ Cs * R n) →
      (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x,
          qs n < metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) ε C1s C2s
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
          ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      ∀ {Cg εg C1g C2g : ℝ} {Ctg : ℝ≥0}, 0 < Cg → εg ≤ coneAccuracy →
      ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
          seedTrace y R L εg C1g C2g
        Ctg →
      ∀ {Cgrad : ℝ≥0}, C2g ≤ (Cgrad : ℝ) →
      (∀ Rad : ℝ, ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
            (Rad / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
          (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
          Cg * R n < metricScalarAt
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) x ≤
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) →
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon) (x : ((K n).toHistory.stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
            (a₁ + τ') x) →
      {θ₀ : ℝ} → (hθ₀ : 0 < θ₀) →
      {εK : ℝ} → (hεK : εK ≤ coneAccuracy) → {C1K C2K : ℝ} → {CtimeK CgradK : ℝ≥0} →
      {phiK : ℝ → ℝ} → (hphiK : Perelman.AdmissiblePinchingFunction phiK) →
      {CgK : ℝ} → (hCgK : 1 ≤ CgK) →
      {QK T₀K : ℕ → ℝ} → {pK pFK : ℕ → CutoffParameters} →
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (pK n)} →
      (recordsFK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pFK n)) →
      {a₀K : ℕ → ℝ} →
      (hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
        -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (hδFK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
        (pFK n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
      (haccK : ∀ n : ℕ, (pK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
      (hradK : ∀ n : ℕ, (n : ℝ) + 1 ≤ (pK n).modelRadius) →
      (hordK : ∀ n : ℕ, n + 2 ≤ (pK n).modelOrder) →
      (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (QK n) ≤
        ((recordsK n i hi).static b).neck.scale) →
      (hbirthAK : ∀ᶠ n in atTop, ∀ i hi b,
        1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale) →
      (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
        ((K n).toHistory.event i).incoming.flow
        (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phiK) →
      (hslabK : ∀ n, (K n).EventSlabsDerivative CtimeK (QK n) (Fin.last (K n).eventCount)) →
      (hpinchFK : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀K n)) phiK) →
      (hderFK : ∀ n, (G n).DerivativeBoundBefore CtimeK (QK n) (K n).horizon) →
      (hqRK : ∀ n : ℕ, max ((n : ℝ) + 1) (QK n) ≤ R n) →
      (hT₀K : ∀ B : ℝ, ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - B / R n) →
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
            riemannianEDistOf
                ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                    ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (hPCF : ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
        (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
          (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
        PickedCenterNeighborhood_final_C11PT1 Dw (Dd + Rad) (-σ₁) θ₀ (R n) (CgK * R n) (ρnc n)
          κ εK C1K C2K CgradK (K n) (G n) (σ n) (y n)) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
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
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Ctime phi ε hε hεX hεN hphi K t htl htK G hG D θcap qcan T₀ p pF δb records recordsF yG a₀
    hHI hcan hδF hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt β hβ hβ2 σ y R
    hσ hyG hRn r₀ w hr₀ hw hseed κ hκ ρnc hradii hkappa C1s C2s Cs qs hqs hwitC Tn aSeed haT hsT has
    pT seedTrace L r Cg εg C1g C2g Ctg hCg hεg hgood Cgrad hC2 hseedTop hL hsmall hclock hRr hwin a₁
    ha₁ hpin θ₀ hθ₀ εK hεK C1K C2K CtimeK CgradK phiK hphiK CgK hCgK QK T₀K pK pFK recordsK
    recordsFK a₀K hHIK hcanK hδFK haccK hradK hordK hscaleK hbirthAK hpinchK0 hslabK hpinchFK hderFK
    hqRK hT₀K hdistQC hPCF
  have hRpos : ∀ n, 0 < R n := fun n => by
    rw [hRn n]
    exact (lt_of_lt_of_le (by positivity) (hqcan n)).trans (hqR n)
  exact hdistW_finalSlab_of_hgood_local_P6AN4 hε hεX hεN hphi htl htK hG recordsF hHI hcan hδF
    hqcan hpar hscale hbirthA hθcap hpinch hslab hderG hqR hnot hT₀ hRt hβ hβ2
    (fun n => (K n).toHistory) rfl σ y R hσ hyG hRn hr₀ hw hseed hκ ρnc hradii hkappa hqs hwitC
    (ObservedHistory.hbcadC_final_of_pickedCenter_P6TF (C1 := C1K) (C2 := C2K) (Cgrad := CgradK)
      hθ₀ hεK hκ hphiK hCgK (fun n => (htl n).trans (htK n)) hG recordsFK hHIK hcanK hδFK haccK
      hradK hordK hscaleK hbirthAK hpinchK0 hslabK hpinchFK hderFK σ y R hRpos hqRK hT₀K Tn aSeed
      haT hsT has pT seedTrace L hL hwin ρnc hradii hdistQC hPCF)
    Tn aSeed haT hsT has pT seedTrace L r hCg hεg hgood hC2 hseedTop hL hsmall hclock hRr hwin
    ha₁ hpin

end Anchor4Final

/-- consumer（G2，`_P6TF`）：final 构形 `time last < t ≤ … < horizon` 下，T1 final 合同 inhabitant（`Dc = 0`）与
`hbcadC_final_of_pickedCenter_P6TF` 的 `hPCF` 槽同型（只检查形状对齐，不是数学付款）。 -/
example {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (Dw Tc θ₀ Cg ρ κ ε C1 C2 : ℝ) (Cgrad : ℝ≥0) (n : ℕ) :
    PickedCenterNeighborhood_final_C11PT1 Dw 0 Tc θ₀ (R n) (Cg * R n) ρ κ ε C1 C2 Cgrad (K n)
      (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl) (σ n) (y n) :=
  pickedCenterNeighborhood_final_zero_C11PT1 Dw Tc θ₀ (R n) (Cg * R n) ρ κ ε C1 C2 Cgrad (K n) _
    (σ n) (y n)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
