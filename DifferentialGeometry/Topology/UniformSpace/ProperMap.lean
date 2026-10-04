import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.UniformSpace.Cauchy

set_option autoImplicit false

open Filter Topology

theorem IsProperMap.completeSpace {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    [CompleteSpace Y] {f : X → Y} (hf : IsProperMap f) (hu : UniformContinuous f) :
    CompleteSpace X := by
  refine ⟨fun {F} hF => ?_⟩
  have hmap := hF.map hu
  obtain ⟨y, hy⟩ := CompleteSpace.complete hmap
  have : NeBot (F.map f) := hmap.1
  obtain ⟨x, _, hx⟩ := hf.clusterPt_of_mapClusterPt (ClusterPt.of_le_nhds hy)
  exact ⟨x, le_nhds_of_cauchy_adhp hF hx⟩
