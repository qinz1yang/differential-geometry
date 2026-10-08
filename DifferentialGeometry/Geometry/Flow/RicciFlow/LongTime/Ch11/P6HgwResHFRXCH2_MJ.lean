import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResHFRXV11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResDrvHI
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResJ8DriverDTDC_C2

/-!
# hres 事件 / J8 核（CH2 口径）：driver 剩余输入 = HI × J10 × DT（× Cg）（O-CH11-MJ G1，后缀 `_MJ`）

自 W10 草稿 `P6HgwResHFRXV11_C2.lean`（无 DELIVERIES 块）复制后改名；草稿不动。
`HgwResE8_CH2_MJ` = `HgwResE8_V11` 逐字（核 `DrvResE4_DT_V11`；ε / C1 / C2 / Ctime 是参数，CH2 常数口径由槽的
`ε = Γ.epsilon`、`C1 = C1P6 p6X1HN_CH2 Γ` 等等式在引擎侧传入）；桥 `hgwResE4_of_E8_CH2_MJ`。
`HgwResJ8H8_CH2_MJ` = `HgwResJ8H8_V11_CHN` 的 CH2 克隆（`¬HasSTC` 常数组 `p6CoarseCH2_CH2 (p6FineEta ε)`），
核 `DrvResE4_DT_Cg_V11`（Cg := 8）；桥 `hgwResJ8H_CH2_of_J8H8_CH2_MJ` 的目标是 CH2_HPC 底座槽的
`HgwResJ8H_V11_CH2`。逐字缩写 def，非合同 Prop。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6CoarseCH2_CH2)

/-- 开放核 E8（`_V11`）。 -/
def HgwResE8_CH2_MJ
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (ε C1 C2 : ℝ)
    (Ctime _Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ)
    (_Cb _Rn _ζ _δ₀ : ℝ≥0 → ℕ → ℝ) (_m₀ : ℝ≥0 → ℕ → ℕ) (a₀ : ℝ) : Prop :=
  (SurgeryParamCompat_P6PC q 2) ∧
  ∀ records : GC.LongTime.Ch11.CutoffRecords_C11S F q,
    (∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
        D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
        ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
            T₀ ≤ (F.tower.history n).time i.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory i p,
          (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
          ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale) →
    0 < a₀ → (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
    (∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1)) →
    DrvResE4_DT_V11 F q records ε C1 C2 Ctime T₀ Qt a₀

/-- **E8 ⇒ E4（`_V11`）**。 -/
theorem hgwResE4_of_E8_CH2_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ} {a₀ : ℝ}
    (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    (hεle : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hfine :
      ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
        D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
        ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
            T₀ ≤ (F.tower.history n).time i.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory i p,
          (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
          ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    (ha₀ : 0 < a₀)
    (hHI0 : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hT₀δ : ∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1))
    (h : HgwResE8_CH2_MJ F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResE4_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨h.1, hDrvJ_of_drvRes3_DT_HFT hε hεX hεN hεle hC2 hanti hder hfresh records hfine ha₀ hHI0 hT₀δ
      (drvResE3_DT_HFT_of_E4_V11 (h.2 records hfine ha₀ hHI0 hT₀δ)),
    hDext_of_drvRes3_DT_HFT hε hεX hεN hεle hC2 hanti hder hfresh records hfine ha₀ hHI0 hT₀δ
      (drvResE3_DT_HFT_of_E4_V11 (h.2 records hfine ha₀ hHI0 hT₀δ))⟩

/-- 开放核 J8H8（`_V11_CHN`）。 -/
def HgwResJ8H8_CH2_MJ
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (ε C1 C2 : ℝ)
    (Ctime _Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ)
    (_Cb _Rn _ζ _δ₀ : ℝ≥0 → ℕ → ℝ) (_m₀ : ℝ≥0 → ℕ → ℕ) (a₀ : ℝ) : Prop :=
  (SurgeryParamCompat_P6PC q 2) ∧
  ∀ records : GC.LongTime.Ch11.CutoffRecords_C11S F q,
    (∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
        D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
        ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
            T₀ ≤ (F.tower.history n).time i.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory i p,
          (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
          ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale) →
    0 < a₀ → (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
    (∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1)) →
    DrvResE4_DT_Cg_V11 F q records 8 ε C1 C2 Ctime (p6FineEta_C11GT6 ε)
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε)) (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε))
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε)).toNNReal T₀ Qt a₀

/-- **J8H8 ⇒ J8H（`_V11_CHN`）**。 -/
theorem hgwResJ8H_CH2_of_J8H8_CH2_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ} {a₀ : ℝ}
    (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    (hεle : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hfine :
      ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
        D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
        ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
            T₀ ≤ (F.tower.history n).time i.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory i p,
          (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
          ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    (ha₀ : 0 < a₀)
    (hHI0 : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (hT₀δ : ∀ (n : ℕ) (s : ℝ), T₀ n ≤ s → q.delta s ≤ 1 / ((n : ℝ) + 1))
    (h : HgwResJ8H8_CH2_MJ F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResJ8H_V11_CH2 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨h.1, hDrvJ_of_drvRes3_DT_Cg_HFT (Cg := 8) (by norm_num) hε hεX hεN hεle hC2 hanti hder
      hfresh records hfine ha₀ hHI0 hT₀δ
      (drvResE3_DT_Cg_HFT_of_E4_V11 (h.2 records hfine ha₀ hHI0 hT₀δ)),
    hDext_of_drvRes3_DT_Cg_HFT (Cg := 8) (by norm_num) hε hεX hεN hεle hC2 hanti hder
      hfresh records hfine ha₀ hHI0 hT₀δ
      (drvResE3_DT_Cg_HFT_of_E4_V11 (h.2 records hfine ha₀ hHI0 hT₀δ))⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
