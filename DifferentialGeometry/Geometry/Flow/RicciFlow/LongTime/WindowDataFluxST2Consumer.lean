import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.WindowDataFluxST2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.HbarWTop

/-!
# `window_data_flux_of_no_event_ST2` 的跨车道 consumer（lane S-A14-STATIC-2，G1）

只含 `example`（型对齐检查，无常量）：O-W-CURV 的 `hbarW_of_window_flux_CV` 的 `hwin` 参数正是
`window_data_flux_of_no_event_ST2` 对 `PrescribedCuspMeridianTop_CPQ` 字段实例化后的类型。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.CuspP1

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- consumer：Top 版 window 数据（含 `hvel`）一行喂给 O-W-CURV 的 `hbarW_of_window_flux_CV`。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) :=
  M.hbarW_of_window_flux_CV fun ht₀ hreg =>
    window_data_flux_of_no_event_ST2 cores M.exterior M.model M.port M.loop M.transported
      M.prescribed ht₀ hreg

end GC.LongTime.CuspP1
