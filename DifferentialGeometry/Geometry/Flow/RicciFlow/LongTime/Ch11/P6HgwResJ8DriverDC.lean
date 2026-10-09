import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverCgDC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResD0V11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResD0CHN

/-!
# J8 核的 driver 剩余输入孪生（`_DC`）

DRVWIRE GAP (a)：J8 核 `HgwResJ8H_V11` / `HgwResJ8H_V11_CHN` 的孪生（去 driver 输出项，E5 式）：
第 2、3 合取（hDrvJ8 / hDext8）→ `DrvResE_Cg_DC F q records 8 …`（引擎以 SCRS⁺ 解包的同一 `records`
实例化，带细窗口投影 `hfine`）。`hgwResJ8H_V11{,_CHN}_of_J8H5_DC`：J8H5 + 引擎级项（ε 三门槛、`0 ≤ C2`、
`hanti`、`hder`、`hfresh`、`records`、`hfine`）⇒ J8H。**无新 binder**。
生成器 `build-logs/scratch/DRVCG8/gen/g5.py`。
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

open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6CoarseCHN_CHN)

/-- 开放核 J8H5（`_V11_DC`）：`HgwResJ8H_V11` 的第 2、3 合取（hDrvJ8 / hDext8）→ driver 剩余输入核
`DrvResE_Cg_DC`（`Cg := 8`，`¬ HasSTC` 取粗常数 `p6CoarseC_C11GT6`）。逐字缩写 def，非合同 Prop。 -/
def HgwResJ8H5_V11_DC
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (ε C1 C2 : ℝ)
    (Ctime _Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ)
    (_Cb _Rn _ζ _δ₀ : ℝ≥0 → ℕ → ℝ) (_m₀ : ℝ≥0 → ℕ → ℕ) (_a₀ : ℝ) : Prop :=
  (SurgeryParamCompat_P6PC q 2) ∧
  ∀ records : GC.LongTime.Ch11.CutoffRecords_C11S F q,
    (∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
        D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
        ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
            T₀ ≤ (F.tower.history n).time i.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory i p,
          (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
          ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale) →
    DrvResE_Cg_DC F q records 8 ε C1 C2 Ctime (p6FineEta_C11GT6 ε)
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)) (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
      (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal T₀ Qt

/-- **J8H5 ⇒ J8H（`_V11_DC`）**：第 2、3 合取由 `hDrvJ_of_drvRes_Cg_DC` / `hDext_of_drvRes_Cg_DC`
（`Cg := 8`，`4 ≤ 8`）给出。 -/
theorem hgwResJ8H_V11_of_J8H5_DC {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (h : HgwResJ8H5_V11_DC F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResJ8H_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨h.1, hDrvJ_of_drvRes_Cg_DC (Cg := 8) (by norm_num) hε hεX hεN hεle hC2 hanti hder
      hfresh records hfine (h.2 records hfine),
    hDext_of_drvRes_Cg_DC (Cg := 8) (by norm_num) hε hεX hεN hεle hC2 hanti hder
      hfresh records hfine (h.2 records hfine)⟩

/-- 开放核 J8H5（`_V11_CHN_DC`）：`HgwResJ8H_V11_CHN` 的第 2、3 合取（hDrvJ8 / hDext8）→ driver 剩余输入核
`DrvResE_Cg_DC`（`Cg := 8`，`¬ HasSTC` 取粗常数 `p6CoarseCHN_CHN`）。逐字缩写 def，非合同 Prop。 -/
def HgwResJ8H5_V11_CHN_DC
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) (ε C1 C2 : ℝ)
    (Ctime _Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ)
    (_Cb _Rn _ζ _δ₀ : ℝ≥0 → ℕ → ℝ) (_m₀ : ℝ≥0 → ℕ → ℕ) (_a₀ : ℝ) : Prop :=
  (SurgeryParamCompat_P6PC q 2) ∧
  ∀ records : GC.LongTime.Ch11.CutoffRecords_C11S F q,
    (∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
        D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
        ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
            T₀ ≤ (F.tower.history n).time i.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory i p,
          (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
          ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale) →
    DrvResE_Cg_DC F q records 8 ε C1 C2 Ctime (p6FineEta_C11GT6 ε)
      (p6CoarseCHN_CHN.{u} (p6FineEta_C11GT6 ε)) (p6CoarseCHN_CHN.{u} (p6FineEta_C11GT6 ε))
      (p6CoarseCHN_CHN.{u} (p6FineEta_C11GT6 ε)).toNNReal T₀ Qt

/-- **J8H5 ⇒ J8H（`_V11_CHN_DC`）**：第 2、3 合取由 `hDrvJ_of_drvRes_Cg_DC` / `hDext_of_drvRes_Cg_DC`
（`Cg := 8`，`4 ≤ 8`）给出。 -/
theorem hgwResJ8H_V11_CHN_of_J8H5_DC {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (h : HgwResJ8H5_V11_CHN_DC F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResJ8H_V11_CHN F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨h.1, hDrvJ_of_drvRes_Cg_DC (Cg := 8) (by norm_num) hε hεX hεN hεle hC2 hanti hder
      hfresh records hfine (h.2 records hfine),
    hDext_of_drvRes_Cg_DC (Cg := 8) (by norm_num) hε hεX hεN hεle hC2 hanti hder
      hfresh records hfine (h.2 records hfine)⟩
end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
