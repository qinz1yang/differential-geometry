import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfSuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.CanonicalWindowsSupplyC11RB

set_option autoImplicit false

/-!
# S-CH11-REPROVE-B (consumer)：S3 适配喂进 A12 总装

`exists_surgery_with_decaying_accuracy_of_diagonal_windows_C11RB`：A12 的数据显式版，其中
`hwin`（S3）由 observation 层 windows 经 `canonicalWindowsSupply_of_diagonal_C11RB` 给出；
其余供给仍是显式 binder（S1、S2、S4–S9 由别的车道 / ASM 对接）。另外 `example` 对齐
ASM 的 W1 conjunct 形 `∀ n i b, ((records n i).static b).hasCanonicalWindow`。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set

namespace GC.LongTime.Ch11

universe u

/-- A12 从 observation 层 windows（diagonal 形）：S3 一项被树内适配吃掉。 -/
theorem exists_surgery_with_decaying_accuracy_of_diagonal_windows_C11RB
    {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (p : ℕ → CutoffParameters)
    (old : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i (p n))
    (hwin : ∀ n i b, ((old n i).static b).hasCanonicalWindow)
    (hstatic : ∀ n, (p n).fixed = (p 0).fixed ∧ (p n).modelRadius = (p 0).modelRadius ∧
      (p n).modelOrder = (p 0).modelOrder ∧ (p n).modelAccuracy = (p 0).modelAccuracy ∧
      (p n).recenterConstant = (p 0).recenterConstant)
    (hcompat : ∀ m k : ℕ, m ≤ k → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p k).delta t ∧ (p m).neckRadius t = (p k).neckRadius t ∧
      (p m).protectedRadius t = (p k).protectedRadius t)
    (htime : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).toHistory.time i.succ ≤ (n : ℝ))
    (eps C1 C2 : ℝ) (κ : ℝ → ℝ) (α : ℝ → ℝ → ℝ)
    (hδ : AccuracyDecaySupply_C11S (CutoffParameters.diagonal p).delta)
    (hrad : RadiusAntitoneSupply_C11S (CutoffParameters.diagonal p))
    (hconst : CanonicalConstantsSupply_C11S eps C1 C2)
    (hcan : CanonicalSupply_C11S F (CutoffParameters.diagonal p).neckRadius eps C1 C2)
    (hnc : NoncollapseSupply_C11S F κ eps)
    (hacc : LargerBallAccuracySupply_C11S (CutoffParameters.diagonal p).delta α)
    (hLB : LargerBallScalarLargeSupply_C11S F (CutoffParameters.diagonal p).delta α)
    (hrcs : RecentCutoffSupply_C11S (diagonalRecords_C11RB F p old hstatic hcompat htime)) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ :=
  exists_surgery_with_decaying_accuracy_of_data_C11S F (CutoffParameters.diagonal p)
    (diagonalRecords_C11RB F p old hstatic hcompat htime) eps C1 C2 κ α hδ hrad
    (canonicalWindowsSupply_of_diagonal_C11RB F p old hwin hstatic hcompat htime)
    hconst hcan hnc hacc hLB hrcs

/-- 与 ASM 的 W1 conjunct 形对齐：S3 展开就是 `∀ n i b, … hasCanonicalWindow`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} (records : CutoffRecords_C11S F q)
    (h : CanonicalWindowsSupply_C11S records) :
    ∀ n i b, ((records n i).static b).hasCanonicalWindow := h

end GC.LongTime.Ch11
