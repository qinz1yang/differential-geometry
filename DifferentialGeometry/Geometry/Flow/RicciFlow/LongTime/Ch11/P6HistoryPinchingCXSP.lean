import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceAnalyticFirstExitCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StatementP6A

set_option autoImplicit false

/-!
# CX-SPINE G21：同一 RawSurgery 的实际 records 生产统一 Hamilton–Ivey

先由固定 initial metric 取 a₀，再任取 F、history 和 records。实际 tower.initial 支付
初始识别，逐 record 的 curvature/scalar preservation 支付全 stageDomain。
不需要 PreparedSpatialStepRetention、BlockTower 或 SCRS⁺。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-- 固定初始数据先选统一年龄常数，同一 F 的实际 records 给全部观测时刻的 HI。 -/
theorem exists_history_pinching_of_records_CXSP (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (F : GC.Interface.RawSurgery P g) (n : ℕ) {params : CutoffParameters}
        (_records : ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params)
        (w : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
        (z : ((F.tower.history n).toHistory.stageAt w).Carrier),
        InFixedHamiltonIveyRegion
          ((F.tower.history n).toHistory.stageMetric
            ((F.tower.history n).toHistory.activeStage w) w) (a₀ + w) z := by
  obtain ⟨a₀, ha₀, hzero⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  refine ⟨a₀, ha₀, ?_⟩
  intro F n params records w z
  let H := (F.tower.history n).toHistory
  have hinit := hzero H (F.tower.initial n)
  have hHI := (H.fixedHamiltonIveyRegion_and_scalar_lower records ha₀ hinit.1 hinit.2).1
  exact (hHI (H.activeStage w) w (H.activeStage_mem w) z).1

end GC.LongTime.Ch11
