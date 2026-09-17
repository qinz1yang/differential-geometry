import Mathlib.Topology.Maps.Proper.Basic

open Set Filter
open scoped Topology

theorem IsProperMap.of_eventuallyEq_cocompact {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f g : X → Y} (hf : IsProperMap f) (hg : Continuous g)
    (heq : g =ᶠ[cocompact X] f) : IsProperMap g := by
  obtain ⟨K, hK, hKeq⟩ := mem_cocompact.mp heq
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨hg, ?_⟩
  intro U y hy
  by_cases hUK : K ∈ U
  · obtain ⟨x, _, hx⟩ := hK.ultrafilter_le_nhds' U hUK
    exact ⟨x, hx⟩
  · have hUKc : Kᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr hUK
    have heqU : g =ᶠ[U] f := by
      filter_upwards [hUKc] with x hx
      exact hKeq hx
    obtain ⟨x, _, hx⟩ := hf.ultrafilter_le_nhds_of_tendsto (hy.congr' heqU)
    exact ⟨x, hx⟩
