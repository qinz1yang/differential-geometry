import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HIPropagationResidueP6HP2

/-!
# DEPTH1 `hpin` 槽（hPN 帧，`a₀ := 0`）的 producer（O-CH11-HP6B-V7 G4b，后缀 `_P6HI`）

从 `P6HinitRecTSlotP6HI` 拆出（lead 07:5x：DEPTH4C 需要，原模块 import 链未入 SNAP）；本模块只 import SNAP root112 内
模块。`hpin_rescaled_of_records_P6HI`（PROVED）：初始 HI（`exists_initialHI_P6WR`）⇒ 重标度初始 HI(a₀/c)
（`rescale_initialHI_P6HP2`）⇒ 全事件 records（`rescale_P6M`）下 HI 传播 HI(a₀/c + τ′)
（`ObservedHistory.hiActive_of_records_P6HP`）⇒ 参数单调到 HI(0 +
    τ′)（`inFixedHamiltonIveyRegion_of_le_P6HP`）。
对一切 n、一切 `c > 0` 成立；结论 = DEPTH1 `hwitC_hderivC_of_hPN_C11G3` 的 hpin 体在 `K n = (F.tower.history (ind
    n))
.rescale_P6N (c n)`、`a₀ := 0` 处的逐点形（DEPTH1 逐字 example 在 `P6HinitRecTSlotP6HI`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **`hpin_rescaled_of_records_P6HI`（PROVED）**：hPN 帧上 DEPTH1 `hpin` 槽（`a₀ := 0`）的 producer。 -/
theorem hpin_rescaled_of_records_P6HI {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (n : ℕ)
    (τ' : Icc (0 : ℝ) ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.horizon)
    (x : (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.stageAt τ').Carrier) :
    InFixedHamiltonIveyRegion
      (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.stageMetric
        (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.activeStage τ') τ') (0 + τ')
            x := by
  obtain ⟨a, ha, hHI⟩ := exists_initialHI_P6WR F
  have hpos : 0 < a / c n := rescaledHIParam_pos_P6HP2 ha (hc n)
  have h := ObservedHistory.hiActive_of_records_P6HP ((F.tower.history (ind n)).rescale_P6N (c n)
      (hc n)).toHistory
    (fun i => (records (ind n) i).rescale_P6M (c n) (hc n)) hpos
    (fun y => (F.tower.history (ind n)).rescale_initialHI_P6HP2 (hc n) 0 ha (hHI (ind n)) y) τ' x
  have hτ : (0 : ℝ) ≤ τ' := τ'.2.1
  exact inFixedHamiltonIveyRegion_of_le_P6HP (by linarith) (by linarith) h

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
