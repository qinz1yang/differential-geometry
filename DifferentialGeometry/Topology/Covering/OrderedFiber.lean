import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Function
open scoped Topology

namespace Poincare.Topology.Covering

theorem injective_of_continuous_fiber_separating_map
    {E X L : Type*} [TopologicalSpace E] [CompactSpace E] [PathConnectedSpace E]
    [TopologicalSpace X] [LinearOrder L] [TopologicalSpace L] [OrderClosedTopology L]
    {f : E → X} (hf : IsCoveringMap f) (g : E → L) (hg : Continuous g)
    (hsep : Function.Injective (fun e ↦ (f e, g e))) : Function.Injective f := by
  obtain ⟨e₀, -, hmin⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set E).Nonempty)
    hg.continuousOn
  have hle (x y : E) (hxy : f x = f y) : g x ≤ g y := by
    by_contra hn
    have hlt : g y < g x := lt_of_not_ge hn
    let γ : Path e₀ x := (PathConnectedSpace.joined e₀ x).somePath
    let β := γ.symm.map hf.continuous
    let δ := hf.liftPath β.toContinuousMap y (β.source.trans hxy)
    have hδ : f ∘ δ = β := hf.liftPath_lifts _ _ _
    have hδ₀ : δ 0 = y := hf.liftPath_zero _ _ _
    let Γ : Path y (δ 1) := ⟨δ, hδ₀, rfl⟩
    have hbase : f ∘ γ = f ∘ Γ.symm := by
      funext t
      have h := congrFun hδ (unitInterval.symm t)
      simpa [β, Γ] using h.symm
    obtain ⟨t, ht⟩ := intermediate_value_univ₂
      (hg.comp γ.continuous) (hg.comp Γ.symm.continuous)
      (show g (γ 0) ≤ g (Γ.symm 0) by simpa using hmin (mem_univ (δ 1)))
      (show g (Γ.symm 1) ≤ g (γ 1) by simpa using hlt.le)
    have hmeet : γ t = Γ.symm t := hsep (Prod.ext (congrFun hbase t) ht)
    have heq := hf.eq_of_comp_eq γ.continuous Γ.symm.continuous hbase t hmeet
    have hend : x = y := by simpa using congrFun heq 1
    exact hlt.ne (congrArg g hend).symm
  intro x y hxy
  exact hsep (Prod.ext hxy (le_antisymm (hle x y hxy) (hle y x hxy.symm)))

end Poincare.Topology.Covering
