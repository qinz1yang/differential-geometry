import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceCone_P6L

/-!
# L6-B G1 consumer：`_P6L` 版在 `U = univ` 时推出原定理

型对齐检查：以原定理的类型（`type_of%`，逐字）为目标，用 `Cone:108_P6L` / `TTC:170_P6L`
在区域 `U n := univ` 上证明之——footprint 形 `hderiv`、`U` 形 `hfinal`、`HEq` 形 `htested`
都由原全局前提直接给出，`hU` 平凡。说明局部化只弱化了前提、没有改结论。
-/

set_option autoImplicit false

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

example :
    type_of% @RetainedCoreHistory.normalized_terminal_ball_volume_lower_bound_of_scaled_tests.{0}
    := by
  intro Phi hPhi C H s G L hinit hs x q Q hq hqQ hQ hderiv hfinal hpinch hpinchFinal rho hbuffer
    κ σ₀ σ hκ hσ₀ hσQ htested
  exact RetainedCoreHistory.normalized_terminal_ball_volume_lower_bound_of_scaled_tests_P6L
    Phi hPhi H s G L hinit hs x q Q hq hqQ hQ (fun _ => univ)
    (fun n j _ _ _ _ _ t ht h => hderiv n j _ t ht h) (fun n y _ => hfinal n y)
    hpinch hpinchFinal (fun _ _ _ => mem_univ _) hbuffer σ hκ hσ₀ hσQ
    (by
      intro n t ht hts A time _ _ y _
      exact htested n t ht hts y)

example :
    type_of% @ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces.{0}
    := by
  intro Phi hPhi C H last s G L hinit x q Q hq hqQ hQ hderiv hfinal hpinch hpinchFinal rho hrho
    hbuffer hvol
  exact ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces_P6L
    Phi hPhi H last s G L hinit x q Q hq hqQ hQ (fun _ => univ)
    (fun n j _ _ _ hl _ _ _ t ht h => hderiv n j hl _ t ht h) (fun n y _ => hfinal n y)
    hpinch hpinchFinal hrho (fun _ _ _ => mem_univ _) hbuffer hvol

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
