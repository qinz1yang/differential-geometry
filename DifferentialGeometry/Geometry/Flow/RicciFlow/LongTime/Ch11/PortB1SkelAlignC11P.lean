import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffParameterGluing

set_option autoImplicit false

/-!
# S-CH11-PORT-B1 G5b：B1 已落地定理与 O-CH11-SKEL 供给表的对齐（`_C11P`）

依赖 O-CH11-SKEL G1 的 `SurgerySuppliesC11S`（只读 import）。检查 B1 的 verbatim 定理的**型**与 SKEL 的
供给谓词逐项相合：

* S1 `AccuracyDecaySupply_C11S`：`diagonal_delta_eq` + SKEL 的 `accuracyDecaySupply_of_tendsto_C11S`；
* S2 `RadiusAntitoneSupply_C11S`：`CutoffParameters.diagonal_neckRadius_antitone` 的结论就是它；
* S5（history 形）`HistoryCanonicalSupply_C11S`：`h n` 正是
  `exists_localized_canonical_time_control_point_selection` 的 `hcanonical` 实参
  （`H := (F.tower.history n).toHistory`，`ρ := q.neckRadius`）。

本文件无新声明。S7 / S8 / S9（larger-ball accuracy、A > 1 标量、recent cutoff）在 B1 无对应定理
（它们的 producer 在 B2 / EXT），所以这里不列。
-/

open Set Filter
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime.Ch11

universe u

/-- S2：outer tuple 的 `diagonal` 参数满足 `RadiusAntitoneSupply_C11S`。 -/
example (p : ℕ → CutoffParameters)
    (hcompat : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).neckRadius t = (p n).neckRadius t)
    (hanti : ∀ n : ℕ, AntitoneOn (p n).neckRadius (Icc (0 : ℝ) (n : ℝ))) :
    RadiusAntitoneSupply_C11S (CutoffParameters.diagonal p) :=
  CutoffParameters.diagonal_neckRadius_antitone p hcompat hanti

/-- S1：各层 accuracy 相同且 antitone、趋 0 ⇒ `diagonal` 的 `AccuracyDecaySupply_C11S`。 -/
example (p : ℕ → CutoffParameters) {δ : ℝ → ℝ} (hdelta : ∀ n, (p n).delta = δ)
    (hanti : AntitoneOn δ (Ici 0)) (hlim : Tendsto δ atTop (nhds 0)) :
    AccuracyDecaySupply_C11S (CutoffParameters.diagonal p).delta := by
  rw [CutoffParameters.diagonal_delta_eq p hdelta]
  exact accuracyDecaySupply_of_tendsto_C11S hanti hlim

/-- S5：SKEL 的 history 形 canonical 供给喂给 B1 的 time-control 选点定理的 `hcanonical`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (q : CutoffParameters) {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : NNReal} (hCtime : Ctime ≤ Ctime')
    (hanti : RadiusAntitoneSupply_C11S q)
    (h : HistoryCanonicalSupply_C11S F q.neckRadius eps C1 C2) (n : ℕ) :
    True := by
  have _ := ObservedHistory.exists_localized_canonical_time_control_point_selection
    (F.tower.history n).toHistory q hC1 hC2 hCtime hanti (h n)
  trivial
