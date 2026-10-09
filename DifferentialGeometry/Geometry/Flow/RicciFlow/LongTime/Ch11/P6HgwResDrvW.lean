import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DextDriverDrvW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgwResD0V11

/-!
# DRVWIRE G3a：hres 事件核 E5（`_DW`）——E4 的 driver 输出合取换成 driver 剩余输入

`HgwResE5_DW` = `HgwResE4_V11` 的第 2、3 合取（J11STAY `hDrvJ`、`hDext`）换成
`∀ records : CutoffRecords_C11S F q, hfine(records) → DrvResE_DW F q records …`
（对 SCRS⁺ 给出的粗 records——带细窗口投影 `hfine`——成立；F-24-8：引擎以**同一** SCRS⁺ 解包的
`records` 实例化，与 hgap producer 用的 records 同组）。逐字缩写 def，非合同 Prop。
`hgwResE4_of_E5_DW`：E5 + 引擎级（ε 三门槛、`0 ≤ C2`、`hanti`、`hder`、`hfresh`、`records`、`hfine`）⇒ E4
（经 G2 桥）。生成器 `build-logs/scratch/DRVWIRE/gen/g3.py`。
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

/-- 开放核 E5（`_DW`）：E4 的 `hDrvJ` / `hDext` 合取 → driver 剩余输入核 `DrvResE_DW`。 -/
def HgwResE5_DW
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
    DrvResE_DW F q records ε C1 C2 Ctime T₀ Qt

/-- **E5 ⇒ E4（`_DW`）**：第 2、3 合取由 `hDrvJ_of_drvRes_DW` / `hDext_of_drvRes_DW` 给出。 -/
theorem hgwResE4_of_E5_DW {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    (h : HgwResE5_DW F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀) :
    HgwResE4_V11 F q ε C1 C2 Ctime Ctime₀ T₀ Qt Cb Rn ζ δ₀ m₀ a₀ :=
  ⟨h.1, hDrvJ_of_drvRes_DW hε hεX hεN hεle hC2 hanti hder hfresh records hfine (h.2 records hfine),
    hDext_of_drvRes_DW hε hεX hεN hεle hC2 hanti hder hfresh records hfine (h.2 records hfine)⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
