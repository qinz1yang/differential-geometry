import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Logic.Small.Set
import Mathlib.Data.Countable.Small

universe u v w

theorem ChartedSpace.small_of_lindelofSpace (H : Type u) [TopologicalSpace H] [Small.{w} H]
    (M : Type v) [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M] : Small.{w} M := by
  have hsmall (x : M) : Small.{w} (chartAt H x).source := by
    apply small_of_injective (f := fun y : (chartAt H x).source => chartAt H x y)
    intro a b hab
    exact Subtype.ext ((chartAt H x).injOn a.property b.property hab)
  let _ := hsmall
  obtain ⟨t, htc, ht⟩ := LindelofSpace.elim_nhds_subcover
    (fun x : M => (chartAt H x).source) (chart_source_mem_nhds H)
  let _ : Countable t := htc.to_subtype
  have hs : Small.{w} (⋃ x ∈ t, (chartAt H x).source) := by
    exact small_biUnion.{w} t (fun x _ => (chartAt H x).source)
  rw [ht] at hs
  exact small_univ_iff.mp hs

theorem ChartedSpace.small_of_compactSpace (H : Type u) [TopologicalSpace H] [Small.{w} H]
    (M : Type v) [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] : Small.{w} M :=
  ChartedSpace.small_of_lindelofSpace H M
