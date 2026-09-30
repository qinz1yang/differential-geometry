import DifferentialGeometry.Topology.Manifold.PartialAtlas

open Set Topology TopologicalSpace
open scoped Manifold

namespace DifferentialGeometry.Topology.Manifold.AtlasOn

universe u

variable {H X : Type*} [TopologicalSpace H] [TopologicalSpace X] {G : StructureGroupoid H}

@[instance_reducible] noncomputable def subtypeChartedSpace (s : Opens X)
    (A : AtlasOn G (s : Set X)) :
    ChartedSpace H s where
  atlas := ⋃ x : s, {(A.exists_mem_source x.1 x.2).choose.subtypeRestr ⟨x⟩}
  chartAt x := (A.exists_mem_source x.1 x.2).choose.subtypeRestr ⟨x⟩
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact (A.exists_mem_source x.1 x.2).choose_spec.2
  chart_mem_atlas x := by
    simp only [mem_iUnion, mem_singleton_iff]
    exact ⟨x, rfl⟩

theorem subtypeChartedSpace_hasGroupoid [ClosedUnderRestriction G] (s : Opens X)
    (A : AtlasOn G (s : Set X)) :
    letI := A.subtypeChartedSpace s
    HasGroupoid s G := by
  let _ := A.subtypeChartedSpace s
  constructor
  rintro e e' ⟨_, ⟨x, hc⟩, he⟩ ⟨_, ⟨x', hc'⟩, he'⟩
  rw [hc.symm, mem_singleton_iff] at he
  rw [hc'.symm, mem_singleton_iff] at he'
  rw [he, he']
  refine G.mem_of_eqOnSource ?_
    (OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr (s := s) _ _ _)
  apply closedUnderRestriction'
  · exact A.compatible _ (A.exists_mem_source x.1 x.2).choose_spec.1 _
      (A.exists_mem_source x'.1 x'.2).choose_spec.1
  · exact OpenPartialHomeomorph.isOpen_inter_preimage_symm _ s.2

theorem subtypeRestr_mem_maximalAtlas [ClosedUnderRestriction G] (s : Opens X)
    (A : AtlasOn G (s : Set X)) (hs : Nonempty s) {e : OpenPartialHomeomorph X H}
    (he : e ∈ A.charts) :
    letI := A.subtypeChartedSpace s
    e.subtypeRestr hs ∈ G.maximalAtlas s := by
  let _ := A.subtypeChartedSpace s
  rintro e' ⟨_, ⟨x, hc⟩, he'⟩
  rw [hc.symm, mem_singleton_iff] at he'
  rw [he']
  have hx := (A.exists_mem_source x.1 x.2).choose_spec.1
  constructor
  · refine G.mem_of_eqOnSource ?_
      (OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr (s := s) _ _ _)
    exact closedUnderRestriction' (A.compatible _ he _ hx)
      (OpenPartialHomeomorph.isOpen_inter_preimage_symm _ s.2)
  · refine G.mem_of_eqOnSource ?_
      (OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr (s := s) _ _ _)
    exact closedUnderRestriction' (A.compatible _ hx _ he)
      (OpenPartialHomeomorph.isOpen_inter_preimage_symm _ s.2)

end DifferentialGeometry.Topology.Manifold.AtlasOn
