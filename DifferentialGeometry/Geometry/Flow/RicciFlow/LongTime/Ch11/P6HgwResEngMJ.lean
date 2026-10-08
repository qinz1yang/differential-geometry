import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResThMJ
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResE4ThEngMJ

/-!
# MJ G3 观察：引擎直接供给 J / J8 结论形（无槽，后缀 `_MJ`）

`P6DrvResE4ThEngMJ`：θ₀ 尾核亦由引擎数据证出。故 `HgwResE4_V11` / `HgwResJ8H_V11_CH2`（引擎所需结论形）可由
引擎数据直接给出（`hpc` 由引擎 `hcap` 付），不再需要 `hresJ` / `hresJ8` 槽。本文件：两条直接供给定理。
PROVED 相对 `hrcs`、`hδq`、`hfine`、TDS `hder`、`ha₀`/`hHI`、`T₀ ≥ thetaJ_MJ`、`T₀ ≥ recentThrN_HNS (n+1)`、
`T₀ ≥ lateLambdaThr`。无新 binder / Prop；这是 `MJ2`（5 binder）之外的可选形（去 2 个 binder），
是否采用由 lead 裁定。
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

/-- **引擎直接供给 `HgwResE4_V11`（无 `hresJ` 槽，`_MJ`，PROVED 相对 `hrcs`、`hδq`、`hfine`、`hder`、
`T₀ ≥ thetaJ_MJ / recentThrN_HNS (n+1) / lateLambdaThr`）**。 -/
theorem hgwResE4_of_engine_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hpc : SurgeryParamCompat_P6PC q 2)
    (hTr : ∀ n, recentThrN_HNS hrcs (fun m : ℕ => (m : ℝ) + 1) n ≤ T₀ n)
    (hΛ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) :
    HgwResE4_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ := by
  have hE4 : DrvResE4_DT_V11 F q records ε C1 C2 Ctime T₀ Qt a₀ :=
    drvResE4_DT_of_Th_MJ hε hε' hC1 hC2' hCt hC2 hanti hder hrcs hδq hfine ha₀ hHI0 hT
    (drvResE4_DT_Th_of_engine_MJ (Qt := Qt) hanti hrcs hδq hTr hΛ)
  exact ⟨hpc, hDrvJ_of_drvRes3_DT_HFT hε hεX hεN hεle hC2 hanti hder hfresh records hfine ha₀
      hHI0 hT₀δ (drvResE3_DT_HFT_of_E4_V11 hE4),
    hDext_of_drvRes3_DT_HFT hε hεX hεN hεle hC2 hanti hder hfresh records hfine ha₀ hHI0 hT₀δ
      (drvResE3_DT_HFT_of_E4_V11 hE4)⟩

/-- **引擎直接供给 `HgwResJ8H_V11_CH2`（无 `hresJ8` 槽，`_MJ`，PROVED 相对同 `hgwResE4_of_engine_MJ`）**；
元组由 `(εb, Ctime)` 定出，`εb = p6FineEta ε`。 -/
theorem hgwResJ8H_of_engine_MJ {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (hpc : SurgeryParamCompat_P6PC q 2)
    (hTr : ∀ n, recentThrN_HNS hrcs (fun m : ℕ => (m : ℝ) + 1) n ≤ T₀ n)
    (hΛ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) :
    HgwResJ8H_V11_CH2 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ := by
  have hE4 : DrvResE4_DT_Cg_V11 F q records 8 ε C1 C2 Ctime (p6FineEta_C11GT6 ε)
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε)) (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε))
      (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 ε)).toNNReal T₀ Qt a₀ :=
    drvResE4_DT_Cg_of_Th_MJ hη hη' hC1 hC1 hCt hC2 hanti hder hrcs hδq hfine ha₀ hHI0 hT
    (drvResE4_DT_Cg_Th_of_engine_MJ (Qt := Qt) hanti hrcs hδq hTr hΛ)
  exact ⟨hpc, hDrvJ_of_drvRes3_DT_Cg_HFT (Cg := 8) (by norm_num) hε hεX hεN hεle hC2 hanti hder
      hfresh records hfine ha₀ hHI0 hT₀δ (drvResE3_DT_Cg_HFT_of_E4_V11 hE4),
    hDext_of_drvRes3_DT_Cg_HFT (Cg := 8) (by norm_num) hε hεX hεN hεle hC2 hanti hder
      hfresh records hfine ha₀ hHI0 hT₀δ (drvResE3_DT_Cg_HFT_of_E4_V11 hE4)⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
