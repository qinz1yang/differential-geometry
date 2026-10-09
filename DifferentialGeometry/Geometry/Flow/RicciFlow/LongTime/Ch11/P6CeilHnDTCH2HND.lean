import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResDiagDTRXHND
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResDiagDTCgHND
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnSpecCH2

set_option autoImplicit false

/-!
# HNOTDT G3：DT 线 / DT+Cg 行 hnot 合取的 ceiling 版（`_HND`）

CEILHN2 `hnR_dominated_CH2` / `hnR_dominated_fine_CH2` 给出 `csHNR ≤ ceiling`、`ctHNR ≤ ceiling`；
`csSeq_CH2 ≤ csHNR_CH2`、`ctSeq_CH2 ≤ ctHNR_CH2`（`csSeq_le_csHNR_CH2` / `ctSeq_le_ctHNR_CH2`）。
故 `drvDTRX_HNO_at_seq_HND` / `drvDTCg_HNO_at_seq_HND` 的三条常数前提在 ceiling 内由 `HN` 支配付：

* `drvDTRX_HNO_at_ceiling_HND`：DT 行，`Γ.epsilon` 处；
* `drvDTCg_HNO_at_ceiling_HND`：DT+Cg 行（J8），`¬HasSTC` 常数组 `εb = Γ.epsilon`
  在 ceiling `X1HN / X2HN / p6CtimeHN`；
* `drvDTCg_HNO_at_ceiling_fine_HND`：DT+Cg 行，`εb = p6FineEta Γ.epsilon`，常数 `Cf′ = p6CoarseCH2 ηf`。
无新顶层 binder，无新 Prop；`hanti`、`hder` 同 `hslabK_of_tds_HND`（桥原有）。
-/

noncomputable section

open Set
open GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-- **DT 行 hnot 合取，ceiling 版（PROVED）**。 -/
theorem drvDTRX_HNO_at_ceiling_HND (Γ : ClosedBirthConstants)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : CutoffRecords_C11S F q}
    {C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Ctd : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctd)
    (h1 : C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ≤ C1) (h2 : C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ≤ C2)
    (h3 : p6CtimeHN_CH2.{u} Γ ≤ Ctime)
    (h : DrvResE_DT_RX_HSX_HNR F q records Γ.epsilon C1 C2 Ctime T₀ Qt) :
    DrvResE_DT_RX_HSX_HNO F q records Γ.epsilon C1 C2 Ctime T₀ Qt :=
  drvDTRX_HNO_at_seq_HND.{u} (epsilon_mem_C11GT6 Γ).1 (epsilon_mem_C11GT6 Γ).2 hanti hder
    ((csSeq_le_csHNR_CH2.{u} _).trans ((hnR_dominated_CH2.{u} Γ).1.trans h1))
    ((csSeq_le_csHNR_CH2.{u} _).trans ((hnR_dominated_CH2.{u} Γ).2.1.trans h2))
    ((ctSeq_le_ctHNR_CH2.{u} _).trans ((hnR_dominated_CH2.{u} Γ).2.2.trans h3)) h

/-- **DT+Cg 行（J8）hnot 合取，ceiling 版（PROVED）**：`εb = Γ.epsilon`。 -/
theorem drvDTCg_HNO_at_ceiling_HND (Γ : ClosedBirthConstants)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Ctd : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctd)
    (h1 : C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ≤ C1b) (h2 : C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ≤ C2b)
    (h3 : p6CtimeHN_CH2.{u} Γ ≤ Ctimeb)
    (h : DrvResE_DT_Cg_RX_HSX_HNR F q records Cg ε C1 C2 Ctime Γ.epsilon C1b C2b Ctimeb T₀ Qt) :
    DrvResE_DT_Cg_RX_HSX_HNO F q records Cg ε C1 C2 Ctime Γ.epsilon C1b C2b Ctimeb T₀ Qt :=
  drvDTCg_HNO_at_seq_HND.{u} (epsilon_mem_C11GT6 Γ).1 (epsilon_mem_C11GT6 Γ).2 hanti hder
    ((csSeq_le_csHNR_CH2.{u} _).trans ((hnR_dominated_CH2.{u} Γ).1.trans h1))
    ((csSeq_le_csHNR_CH2.{u} _).trans ((hnR_dominated_CH2.{u} Γ).2.1.trans h2))
    ((ctSeq_le_ctHNR_CH2.{u} _).trans ((hnR_dominated_CH2.{u} Γ).2.2.trans h3)) h

/-- **DT+Cg 行（J8/JF8 坏点帧）hnot 合取，ceiling 版（PROVED）**：`εb = ηf := p6FineEta Γ.epsilon`，
`C1b, C2b ≥ Cf′`、`Ctimeb ≥ Cf′ᵗᵒᴺᴺ`。 -/
theorem drvDTCg_HNO_at_ceiling_fine_HND (Γ : ClosedBirthConstants)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Ctd : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctd)
    (h1 : p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ C1b)
    (h2 : p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ C2b)
    (h3 : (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ≤ Ctimeb)
    (h : DrvResE_DT_Cg_RX_HSX_HNR F q records Cg ε C1 C2 Ctime (p6FineEta_C11GT6 Γ.epsilon)
      C1b C2b Ctimeb T₀ Qt) :
    DrvResE_DT_Cg_RX_HSX_HNO F q records Cg ε C1 C2 Ctime (p6FineEta_C11GT6 Γ.epsilon)
      C1b C2b Ctimeb T₀ Qt :=
  drvDTCg_HNO_at_seq_HND.{u} (p6FineEta_pos_C11GT6 (epsilon_mem_C11GT6 Γ).1)
    (p6FineEta_lt_eleventh_C11G2 Γ) hanti hder
    ((csSeq_le_csHNR_CH2.{u} _).trans ((hnR_dominated_fine_CH2.{u} Γ).1.trans h1))
    ((csSeq_le_csHNR_CH2.{u} _).trans ((hnR_dominated_fine_CH2.{u} Γ).1.trans h2))
    ((ctSeq_le_ctHNR_CH2.{u} _).trans ((hnR_dominated_fine_CH2.{u} Γ).2.trans h3)) h

/-- consumer（DT 行与 DT+Cg 行）：同一 `_HNR` 孪生同时给出原核与 `_HNO`（ceiling 内）。 -/
example (Γ : ClosedBirthConstants)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : CutoffRecords_C11S F q}
    {C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Ctd : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctd)
    (h1 : C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ≤ C1) (h2 : C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ≤ C2)
    (h3 : p6CtimeHN_CH2.{u} Γ ≤ Ctime)
    (h : DrvResE_DT_RX_HSX_HNR F q records Γ.epsilon C1 C2 Ctime T₀ Qt) :
    DrvResE_DT_RX_HSX F q records Γ.epsilon C1 C2 Ctime T₀ Qt ∧
      DrvResE_DT_RX_HSX_HNO F q records Γ.epsilon C1 C2 Ctime T₀ Qt :=
  ⟨drvDTRX_of_HNR h, drvDTRX_HNO_at_ceiling_HND Γ hanti hder h1 h2 h3 h⟩

example (Γ : ClosedBirthConstants)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : CutoffRecords_C11S F q}
    {Cg ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1b C2b : ℝ} {Ctimeb : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Ctd : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctd)
    (h1 : C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ≤ C1b) (h2 : C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ≤ C2b)
    (h3 : p6CtimeHN_CH2.{u} Γ ≤ Ctimeb)
    (h : DrvResE_DT_Cg_RX_HSX_HNR F q records Cg ε C1 C2 Ctime Γ.epsilon C1b C2b Ctimeb T₀ Qt) :
    DrvResE_DT_Cg_RX_HSX F q records Cg ε C1 C2 Ctime Γ.epsilon C1b C2b Ctimeb T₀ Qt ∧
      DrvResE_DT_Cg_RX_HSX_HNO F q records Cg ε C1 C2 Ctime Γ.epsilon C1b C2b Ctimeb T₀ Qt :=
  ⟨drvDTCg_of_HNR_HND h, drvDTCg_HNO_at_ceiling_HND Γ hanti hder h1 h2 h3 h⟩

end GC.LongTime.Ch11
