import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false
open Set

variable {𝕜 E F : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F] [PartialOrder F] [TopologicalSpace F]
  [OrderClosedTopology F] [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]

theorem ConvexOn.closure_of_continuousOn {s : Set E} {f : E → F}
    (hf : ConvexOn 𝕜 s f) (hc : ContinuousOn f (closure s)) :
    ConvexOn 𝕜 (closure s) f := by
  have hs : Convex 𝕜 (closure s) := by
    intro x hx y hy a b ha hb hab
    exact map_mem_closure₂ (f := fun u v : E => a • u + b • v) ((continuous_fst.const_smul a).add
      (continuous_snd.const_smul b)) hx hy (fun u hu v hv => hf.1 hu hv ha hb hab)
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hleft : ContinuousOn (fun w : E × E => f (a • w.1 + b • w.2)) (closure (s ×ˢ s)) :=
    hc.comp ((continuous_fst.const_smul a).add (continuous_snd.const_smul b)).continuousOn
      (by intro w hw; rw [closure_prod_eq] at hw; exact hs hw.1 hw.2 ha hb hab)
  have hfst : ContinuousOn (fun w : E × E => f w.1) (closure (s ×ˢ s)) :=
    hc.comp continuous_fst.continuousOn
      (by intro w hw; rw [closure_prod_eq] at hw; exact hw.1)
  have hsnd : ContinuousOn (fun w : E × E => f w.2) (closure (s ×ˢ s)) :=
    hc.comp continuous_snd.continuousOn
      (by intro w hw; rw [closure_prod_eq] at hw; exact hw.2)
  exact le_on_closure (fun w hw => hf.2 hw.1 hw.2 ha hb hab)
    hleft ((hfst.const_smul a).add (hsnd.const_smul b))
    (show (x, y) ∈ closure (s ×ˢ s) by rw [closure_prod_eq]; exact ⟨hx, hy⟩)
