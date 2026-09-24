import DifferentialGeometry.Topology.Connected.Frontier

open Set Topology

namespace DifferentialGeometry.Topology

theorem inter_interior_eq_of_subset_of_local_frontier_subset
    {X : Type*} [TopologicalSpace X] {R A V : Set X} {x : X}
    (hRA : R ⊆ A) (hx : x ∈ closure (interior R)) (hV : V ∈ 𝓝 x)
    (hconn : IsPreconnected (V ∩ interior A))
    (hfront : V ∩ frontier R ⊆ frontier A) :
    V ∩ interior R = V ∩ interior A := by
  have hint := interior_mono hRA
  have hdis : Disjoint (V ∩ interior A) (frontier R) := by
    refine disjoint_left.mpr fun y hy hyR => ?_
    exact (hfront ⟨hy.1, hyR⟩).2 hy.2
  obtain ⟨y, hyV, hyR⟩ := mem_closure_iff_nhds.mp hx V hV
  have hsub := subset_interior_of_isPreconnected_of_disjoint_frontier hconn hdis
    ⟨y, ⟨hyV, hint hyR⟩, hyR⟩
  exact Subset.antisymm (inter_subset_inter_right V hint)
    (fun _ hy => ⟨hy.1, hsub hy⟩)

theorem inter_interior_eq_compl_of_local_frontier_subset
    {X : Type*} [TopologicalSpace X] {R A V : Set X} {x : X}
    (hA : closure (interior A) = A) (hRA : R ∩ A ⊆ frontier A)
    (hx : x ∈ closure (interior R)) (hV : V ∈ 𝓝 x)
    (hconn : IsPreconnected (V ∩ Aᶜ))
    (hfront : V ∩ frontier R ⊆ frontier A) :
    V ∩ interior R = V ∩ Aᶜ := by
  have hAC : IsClosed A := hA ▸ isClosed_closure
  have hsub : R ⊆ (interior A)ᶜ := fun y hy hya =>
    (hRA ⟨hy, interior_subset hya⟩).2 hya
  have hint : interior R ⊆ Aᶜ := by
    have h := interior_mono hsub
    rwa [interior_compl, hA] at h
  have hdis : Disjoint (V ∩ Aᶜ) (frontier R) := by
    refine disjoint_left.mpr fun y hy hyR => ?_
    exact hy.2 (hAC.frontier_subset (hfront ⟨hy.1, hyR⟩))
  obtain ⟨y, hyV, hyR⟩ := mem_closure_iff_nhds.mp hx V hV
  have hback := subset_interior_of_isPreconnected_of_disjoint_frontier hconn hdis
    ⟨y, ⟨hyV, hint hyR⟩, hyR⟩
  exact Subset.antisymm (inter_subset_inter_right V hint)
    (fun _ hy => ⟨hy.1, hback hy⟩)

end DifferentialGeometry.Topology
