import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceCone3_P6L

/-!
# L6-B G2 consumer：`Cone:258_P6L` / `Cone:365_P6L` 在 `U = univ` 时推出原定理

型对齐检查：目标为原定理类型（`type_of%`，逐字），用 `_P6L` 版取 `U n := univ` 证出。
-/

set_option autoImplicit false

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

example :
    type_of% @RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_scaled_tests.{0}
    := by
  intro Phi hPhi C H s G L hinit hs x q Q hscale hq hqQ hQ hderiv hfinal hpinch hpinchFinal rho
    hrho hbuffer κ σ₀ σ hκ hσ₀ hσQ htested
  exact RetainedCoreHistory.exists_normalized_terminal_pointed_convergence_of_scaled_tests_P6L
    Phi hPhi H s G L hinit hs x q Q hscale hq hqQ hQ (fun _ => univ)
    (fun n j _ _ _ _ _ t ht h => hderiv n j _ t ht h) (fun n y _ => hfinal n y)
    hpinch hpinchFinal hrho (fun _ _ _ => mem_univ _) hbuffer σ hκ hσ₀ hσQ
    (by
      intro n t ht hts A time _ _ y _
      exact htested n t ht hts y)

example :
    type_of%
      @RetainedCoreHistory.exists_nonnegative_local_flow_with_comparison_of_final_slab_window.{0, 0}
    := by
  intro H s A hinit Ctime q hq hderiv hfinal x Q hQ hqQ hQlim Phi hPhi hpinch hpinchFinal hbuffer
    hs hscale κ σ₀ σ hκ hσ₀ hσQ htested N _ _ _ _ Hn xN B R hR hBsource hBbase hcapture hBconv
  exact RetainedCoreHistory.exists_nonnegative_local_flow_with_comparison_of_final_slab_window_P6L
    H s A hinit Ctime q hq (fun _ => univ) (fun n j _ _ _ _ _ t ht h => hderiv n j _ t ht h)
    (fun n y _ => hfinal n y) x Q hQ hqQ hQlim (fun _ _ _ => mem_univ _) hPhi hpinch hpinchFinal
    hbuffer hs hscale σ hκ hσ₀ hσQ
    (by
      intro n t ht hts B' tm _ _ y _
      exact htested n t ht hts y)
    Hn xN B hR hBsource hBbase hcapture hBconv

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
