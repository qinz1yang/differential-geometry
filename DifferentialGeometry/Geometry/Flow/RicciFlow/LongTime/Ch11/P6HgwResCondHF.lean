import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverCondHF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResDrvHI
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResD0V11

/-!
# HFIN G5a：hres 事件核 E7（`_HF`）——E6 的 `DrvResE2_DW` 换成 `DrvResE3_HF`（GAP e 退场）

`HgwResE7_HF` = `HgwResE6_DH` 逐字，核 `DrvResE2_DW` → `DrvResE3_HF`（`hfin` + `G` 退场，final
`hderF` 条件形）。`hgwResE4_of_E7_HF`：E7 + 引擎级项 ⇒ E4（经 `hDrvJ_of_drvRes3_HF` / `hDext_of_drvRes3_HF`）。
`hgwResE7_of_E6_HF`：E6 ⇒ E7（新核更弱，经 `drvRes3_of_drvRes2_HF`）。
生成器 `build-logs/scratch/HFIN/gen/g5.py`（源 sha256
    `f8ad2afe2cd8319cd59b366948bdb495612aa9773b4dc44c444c257914124e64`）。
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

/-- 开放核 E7（`_HF`）：E6 的核 `DrvResE2_DW` → `DrvResE3_HF`（GAP e 条件形）。 -/
def HgwResE7_HF
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
    DrvResE3_HF F q records ε C1 C2 Ctime T₀ Qt a₀

/-- **E7 ⇒ E4（`_HF`）**：第 2、3 合取由 `hDrvJ_of_drvRes3_HF` / `hDext_of_drvRes3_HF` 给出。 -/
theorem hgwResE4_of_E7_HF {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (h : HgwResE7_HF F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResE4_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨h.1, hDrvJ_of_drvRes3_HF hε hεX hεN hεle hC2 hanti hder hfresh records hfine ha₀ hHI0 hT₀δ
      (h.2 records hfine ha₀ hHI0 hT₀δ),
    hDext_of_drvRes3_HF hε hεX hεN hεle hC2 hanti hder hfresh records hfine ha₀ hHI0 hT₀δ
      (h.2 records hfine ha₀ hHI0 hT₀δ)⟩

/-- **E6 ⇒ E7（`_HF`，PROVED）**：新核更弱（`drvRes3_of_drvRes2_HF`）。 -/
theorem hgwResE7_of_E6_HF {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ}
    {Ctime Ctime₀ : ℝ≥0} {T₀ Qt : ℕ → ℝ} {Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ} {m₀ : ℝ≥0 → ℕ → ℕ} {a₀ : ℝ}
    (h : HgwResE6_DH F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResE7_HF F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨h.1, fun records hfine ha₀ hHI0 hT₀δ =>
    drvRes3_of_drvRes2_HF (h.2 records hfine ha₀ hHI0 hT₀δ)⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
