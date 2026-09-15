import Mathlib.Topology.SeparatedMap

open Filter
open scoped Topology

theorem IsLocallyInjective.eventuallyEq_of_comp_eventuallyEq
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {π : β → γ} (hπ : IsLocallyInjective π)
    {f g : α → β} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hx : f x = g x) (heq : (π ∘ f) =ᶠ[𝓝 x] (π ∘ g)) : f =ᶠ[𝓝 x] g := by
  obtain ⟨U, hU, hxU, hUinj⟩ := hπ (f x)
  have hfU : ∀ᶠ y in 𝓝 x, f y ∈ U := hf (hU.mem_nhds hxU)
  have hgU : ∀ᶠ y in 𝓝 x, g y ∈ U := hg (hU.mem_nhds (hx ▸ hxU))
  filter_upwards [hfU, hgU, heq] with y hyf hyg hyeq
  exact hUinj hyf hyg hyeq
