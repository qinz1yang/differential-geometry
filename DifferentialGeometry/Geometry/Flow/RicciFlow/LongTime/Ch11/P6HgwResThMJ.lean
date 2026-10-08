import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResE4ThCgMJ
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResHFRXCH2_MJ
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResDTV11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnSpecCH2

/-!
# MJ G2：hresJ / hresJ8 槽核（θ₀ 尾核形，CH2 口径，后缀 `_MJ`）

`HgwResE8_Th_MJ` / `HgwResJ8H8_Th_MJ`：槽核由 `DrvResE4_DT{,_Cg}_V11` 换成 θ₀ 尾核
`DrvResE4_DT{,_Cg}_Th_MJ`（records / J10 / hnot 合取由引擎供给，见 `P6DrvResE4ThMJ`）。槽前提段
（`SurgeryParamCompat`、`records`、`hfine`、`0 < a₀`、`hHI`、`hT₀δ`）与 `HgwResE8_CH2_MJ` 逐字。

* 桥 `hgwResE4_of_E8_Th_MJ` / `hgwResJ8H_of_J8H8_Th_MJ`：新槽核 ⇒ 引擎所需 `HgwResE4_V11` /
  `HgwResJ8H_V11_CH2`（PROVED，前提 `hrcs`、`hδq`、`T₀ ≥ thetaJ_MJ`、常数 ceiling 比较）；
* 旧核 ⇒ 新核：`hgwResE8Th_of_E8_MJ`（`HgwResE8_CH2_MJ ⇒`）与 `hgwResE8Th_of_E6_MJ`
  （CH2_HPC 底座 `HgwResE6_V11 ⇒`）PROVED（θ₀ 尾合取投影）。J8 行底座 `HgwResJ8H_V11_CH2` 是结论形
  （`hDrvJ ∧ hDext`，无 driver 核），无旧 ⇒ 新方向，只有新 ⇒ 旧（桥）。
* ceiling 常数比较：`csSeq_CH2 ≤ C1/C2`、`ctSeq_CH2 ≤ Ctime`（`Γ.epsilon` 与 `p6FineEta` 两处）。
无新 binder。
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

/-- 开放核 E8（θ₀ 尾核形，`_MJ`）：前提段与 `HgwResE8_CH2_MJ` 逐字，核换 `DrvResE4_DT_Th_MJ`。 -/
def HgwResE8_Th_MJ
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
    DrvResE4_DT_Th_MJ F q records ε C1 C2 Ctime T₀ Qt

/-- 开放核 J8H8（θ₀ 尾核形，CH2，`_MJ`）：前提段与 `HgwResJ8H8_CH2_MJ` 逐字，核换
`DrvResE4_DT_Cg_Th_MJ`（Cg := 8）。 -/
def HgwResJ8H8_Th_MJ
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
    DrvResE4_DT_Cg_Th_MJ F q records 8 ε C1 C2 Ctime (p6FineEta_C11GT6 ε)
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε)) (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε))
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε)).toNNReal T₀ Qt

/-- **旧核 ⇒ 新核（`_MJ`，PROVED）**：`HgwResE8_CH2_MJ ⇒ HgwResE8_Th_MJ`。 -/
theorem hgwResE8Th_of_E8_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ} {a₀ : ℝ}
    (h : HgwResE8_CH2_MJ F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResE8_Th_MJ F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨h.1, fun records hfine ha₀ hHI hδ => drvResE4_Th_of_E4_MJ (h.2 records hfine ha₀ hHI hδ)⟩

/-- **旧核 ⇒ 新核（`_MJ`，PROVED）**：`HgwResJ8H8_CH2_MJ ⇒ HgwResJ8H8_Th_MJ`。 -/
theorem hgwResJ8H8Th_of_J8H8_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ} {a₀ : ℝ}
    (h : HgwResJ8H8_CH2_MJ F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResJ8H8_Th_MJ F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨h.1, fun records hfine ha₀ hHI hδ => drvResE4_Th_Cg_of_E4_MJ (h.2 records hfine ha₀ hHI hδ)⟩

/-- **旧核 ⇒ 新核（`_MJ`，PROVED）**：`DrvResE_DT ⇒ DrvResE4_DT_Th_MJ`（θ₀ 尾合取投影；
CH2_HPC 底座槽核 `HgwResE6_V11` 用）。 -/
theorem drvResE4_Th_of_DT_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {T₀ Qt : ℕ → ℝ} (h : DrvResE_DT F q records ε C1 C2 Ctime T₀ Qt) :
    DrvResE4_DT_Th_MJ F q records ε C1 C2 Ctime T₀ Qt := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, θ₀, hθ₀, hθ⟩ :=
    h A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
      seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
      hball hdistσ hev hlt
  exact ⟨θ₀, hθ₀, hθ⟩

/-- **旧核 ⇒ 新核（`_MJ`，PROVED）**：CH2_HPC 底座槽核 `HgwResE6_V11 ⇒ HgwResE8_Th_MJ`。 -/
theorem hgwResE8Th_of_E6_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ} {a₀ : ℝ}
    (h : HgwResE6_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResE8_Th_MJ F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨h.1, fun records hfine _ _ _ => drvResE4_Th_of_DT_MJ (h.2 records hfine)⟩

/-- ceiling：`csSeq_CH2 Γ.epsilon ≤ C1`（`C1 ≥ C1P6 p6X1HN_CH2`）。 -/
theorem csSeq_le_C1_ceiling_MJ (Γ : GC.GeneralFlow.ClosedBirthConstants) {C1 : ℝ}
    (h : GC.LongTime.Ch11.C1P6_C11GT6.{u} GC.LongTime.Ch11.p6X1HN_CH2.{u} Γ ≤ C1) :
    GC.LongTime.Ch11.csSeq_CH2.{u} Γ.epsilon ≤ C1 :=
  ((GC.LongTime.Ch11.csSeq_le_csHNR_CH2.{u} _).trans
    (GC.LongTime.Ch11.hnR_dominated_CH2.{u} Γ).1).trans h

/-- ceiling：`csSeq_CH2 Γ.epsilon ≤ C2`（`C2 ≥ C2P6 p6X2HN_CH2`）。 -/
theorem csSeq_le_C2_ceiling_MJ (Γ : GC.GeneralFlow.ClosedBirthConstants) {C2 : ℝ}
    (h : GC.LongTime.Ch11.C2P6_C11GT6.{u} GC.LongTime.Ch11.p6X2HN_CH2.{u} Γ ≤ C2) :
    GC.LongTime.Ch11.csSeq_CH2.{u} Γ.epsilon ≤ C2 :=
  ((GC.LongTime.Ch11.csSeq_le_csHNR_CH2.{u} _).trans
    (GC.LongTime.Ch11.hnR_dominated_CH2.{u} Γ).2.1).trans h

/-- ceiling：`ctSeq_CH2 Γ.epsilon ≤ Ctime`（`Ctime ≥ p6CtimeHN_CH2`）。 -/
theorem ctSeq_le_Ctime_ceiling_MJ (Γ : GC.GeneralFlow.ClosedBirthConstants) {Ctime : ℝ≥0}
    (h : GC.LongTime.Ch11.p6CtimeHN_CH2.{u} Γ ≤ Ctime) :
    GC.LongTime.Ch11.ctSeq_CH2.{u} Γ.epsilon ≤ Ctime :=
  ((GC.LongTime.Ch11.ctSeq_le_ctHNR_CH2.{u} _).trans
    (GC.LongTime.Ch11.hnR_dominated_CH2.{u} Γ).2.2).trans h

/-- ceiling（fine 行）：`csSeq_CH2 ηf ≤ p6CoarseCH2_CH2 ηf`（`ηf = p6FineEta Γ.epsilon`）。 -/
theorem csSeq_le_fine_ceiling_MJ (Γ : GC.GeneralFlow.ClosedBirthConstants) :
    GC.LongTime.Ch11.csSeq_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) :=
  (GC.LongTime.Ch11.csSeq_le_csHNR_CH2.{u} _).trans
    (GC.LongTime.Ch11.hnR_dominated_fine_CH2.{u} Γ).1

/-- ceiling（fine 行）：`ctSeq_CH2 ηf ≤ (p6CoarseCH2_CH2 ηf).toNNReal`。 -/
theorem ctSeq_le_fine_ceiling_MJ (Γ : GC.GeneralFlow.ClosedBirthConstants) :
    GC.LongTime.Ch11.ctSeq_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal :=
  (GC.LongTime.Ch11.ctSeq_le_ctHNR_CH2.{u} _).trans
    (GC.LongTime.Ch11.hnR_dominated_fine_CH2.{u} Γ).2

/-- **E8 新槽核 ⇒ 引擎所需 `HgwResE4_V11`（`_MJ`，PROVED 相对 `hrcs`、`hδq`、`T₀ ≥ thetaJ_MJ`）**。 -/
theorem hgwResE4_of_E8_Th_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ} {a₀ : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 11) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) (hεle : ε ≤ coneAccuracy)
    (hC1 : GC.LongTime.Ch11.csSeq_CH2.{u} ε ≤ C1) (hC2' : GC.LongTime.Ch11.csSeq_CH2.{u} ε ≤ C2)
    (hCt : GC.LongTime.Ch11.ctSeq_CH2.{u} ε ≤ Ctime) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hδq : Tendsto q.delta atTop (𝓝 0))
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
    (hT : ∀ n, thetaJ_MJ.{u} records hrcs hanti hδq hfine ha₀ hHI0 hε hε' Ctime n ≤ T₀ n)
    (h : HgwResE8_Th_MJ F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResE4_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ := by
  have hE4 := drvResE4_DT_of_Th_MJ hε hε' hC1 hC2' hCt hC2 hanti hder hrcs hδq hfine ha₀ hHI0 hT
    (h.2 records hfine ha₀ hHI0 hT₀δ)
  exact ⟨h.1, hDrvJ_of_drvRes3_DT_HFT hε hεX hεN hεle hC2 hanti hder hfresh records hfine ha₀
      hHI0 hT₀δ (drvResE3_DT_HFT_of_E4_V11 hE4),
    hDext_of_drvRes3_DT_HFT hε hεX hεN hεle hC2 hanti hder hfresh records hfine ha₀ hHI0 hT₀δ
      (drvResE3_DT_HFT_of_E4_V11 hE4)⟩

/-- **J8H8 新槽核 ⇒ 引擎所需 `HgwResJ8H_V11_CH2`（`_MJ`，PROVED 相对 `hrcs`、`hδq`、
`T₀ ≥ thetaJ_MJ`）**；元组由 `(εb, Ctime)` 定出，`εb = p6FineEta ε`。 -/
theorem hgwResJ8H_of_J8H8_Th_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ} {a₀ : ℝ}
    (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u}) (hεN : ε ≤ crossingNeckAccuracy.{u})
    (hεle : ε ≤ coneAccuracy)
    (hη : 0 < p6FineEta_C11GT6 ε) (hη' : p6FineEta_C11GT6 ε < 1 / 11)
    (hC1 : GC.LongTime.Ch11.csSeq_CH2.{u} (p6FineEta_C11GT6 ε) ≤
      p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε))
    (hCt : GC.LongTime.Ch11.ctSeq_CH2.{u} (p6FineEta_C11GT6 ε) ≤
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε)).toNNReal) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hδq : Tendsto q.delta atTop (𝓝 0))
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
    (hT : ∀ n, thetaJ_MJ.{u} records hrcs hanti hδq hfine ha₀ hHI0 hη hη' Ctime n ≤ T₀ n)
    (h : HgwResJ8H8_Th_MJ F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResJ8H_V11_CH2 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ := by
  have hE4 := drvResE4_DT_Cg_of_Th_MJ hη hη' hC1 hC1 hCt hC2 hanti hder hrcs hδq hfine ha₀ hHI0 hT
    (h.2 records hfine ha₀ hHI0 hT₀δ)
  exact ⟨h.1, hDrvJ_of_drvRes3_DT_Cg_HFT (Cg := 8) (by norm_num) hε hεX hεN hεle hC2 hanti hder
      hfresh records hfine ha₀ hHI0 hT₀δ (drvResE3_DT_Cg_HFT_of_E4_V11 hE4),
    hDext_of_drvRes3_DT_Cg_HFT (Cg := 8) (by norm_num) hε hεX hεN hεle hC2 hanti hder
      hfresh records hfine ha₀ hHI0 hT₀δ (drvResE3_DT_Cg_HFT_of_E4_V11 hE4)⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
