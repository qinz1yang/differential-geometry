import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12EnhancedC11E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.EnhancedBridgeC11M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.A13Final_S153

set_option autoImplicit false

/-!
# O-CH11-MERGE (M3)：A13 由 ch12 终端证出（REPOINT3 wrapper，后缀 `_C11M`）

`late_derivative_tests_of_flow_of_enhanced_C11M` 与 tracked A13 `late_derivative_tests_of_flow`
（`LT/LateCutGeometry.lean:159`，M2-pre 起 `hadm : hasEnhancedAdmissibilityFull_C11F F δ`）**同陈述**
（文件末 `type_of%` 的 `rfl`），证明 = ch12 终端 `A13_of_supplies_S153`，16 项 ch11 供给由 v2 profile 的字段经
`WR/EnhancedBridgeC11M.lean` 逐项给出（按名字传参）。tracked A13 不能原地去 sorry：终端闭包 import
`LateCutGeometry`（成环），故端点调用点改调本定理，原 admission 已删除，独立陈述 `A13EnhancedStatement_C11E` 保留类型回归检查。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime

namespace GC.LongTime.Ch11

universe u

/-- **A13（REPOINT3 wrapper）**：v2 enhanced admissibility + decay ⇒ 每个晚期 cut family 有导数界。 -/
theorem late_derivative_tests_of_flow_of_enhanced_C11M {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : Ch11.hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier)
    (L : LateCutFamily F K slices) : L.hasEventualDerivativeBounds := by
  have hadm' : hasAnalyticAdmissibility F δ := hasAnalyticAdmissibility_of_full_C11F hadm
  obtain ⟨E⟩ := hadm
  exact Ch12.A13_of_supplies_S153 (F := F) (K := K) (hK := hK) (δ := δ) (hadm := hadm')
    (hdec := hdec) (slices := slices) (htimes := htimes) (hnonempty := hnonempty) (L := L)
    (Hp := E.toAnalyticSurgeryProfile)
    (hP1 := p1_O2_of_C11M _ E.linked_windows) (Ctime := E.Ctime)
    (hP2 := p2_O2_of_C11M _ _ E.time_derivative) (hP3 := p3_O2_of_C11M _ E.collar_window)
    (hP4 := p4_O2_of_C11M _ E.epsilon_cone) (hP6 := p6_S23_of_C11M _ E.larger_ball_canonical)
    (hP5 := p5_O13_of_C11M _ E.late_linked_records)
    (hcompat := compat_S58_of_C11M _ E.compatible_cap_records)
    (hStrong := hStrong_of_C11M _ E.strongV1) (hprof := hprof_of_C11M _ E.model_constraints)
    (heps := heps_of_C11M _ E.epsilon_cone) (hRFCa := hRFCa_of_C11M _ E.frontier_collar_full)
    (hCapWin := hCapWin_of_C11M _)

/-- 型对齐：wrapper 与 tracked A13 陈述逐字相同。 -/
example : type_of% @late_derivative_tests_of_flow_of_enhanced_C11M.{u} =
    A13EnhancedStatement_C11E.{u} := rfl

end GC.LongTime.Ch11
