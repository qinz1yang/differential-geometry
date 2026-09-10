import Mathlib.Topology.Connected.Basic

open Set Topology

namespace DifferentialGeometry.Topology

theorem isPreconnected_of_dense_of_locally_preconnected_inter
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {S : Set X}
    (hS : Dense S)
    (hlocal : ∀ x : X, ∃ V ∈ 𝓝 x, IsPreconnected (V ∩ S)) :
    IsPreconnected S := by
  intro U V hU hV hcover hSU hSV
  have hsplit : (S ∩ U) ∪ (S ∩ V) = S := by
    rw [← inter_union_distrib_left, inter_eq_left.mpr hcover]
  have hcoverClosure : (univ : Set X) ⊆ closure (S ∩ U) ∪ closure (S ∩ V) := by
    rw [← closure_union, hsplit, hS.closure_eq]
  obtain ⟨p, hp⟩ := hSU
  obtain ⟨q, hq⟩ := hSV
  obtain ⟨x, _, hxU, hxV⟩ := isPreconnected_closed_iff.mp
    (isPreconnected_univ : IsPreconnected (univ : Set X))
    (closure (S ∩ U)) (closure (S ∩ V)) isClosed_closure isClosed_closure
    hcoverClosure ⟨p, mem_univ _, subset_closure hp⟩ ⟨q, mem_univ _, subset_closure hq⟩
  obtain ⟨N, hN, hconn⟩ := hlocal x
  obtain ⟨y, hyN, hyS, hyU⟩ := mem_closure_iff_nhds.mp hxU N hN
  obtain ⟨z, hzN, hzS, hzV⟩ := mem_closure_iff_nhds.mp hxV N hN
  obtain ⟨w, hw, hwU, hwV⟩ := hconn U V hU hV
    (fun _ hw ↦ hcover hw.2) ⟨y, ⟨hyN, hyS⟩, hyU⟩ ⟨z, ⟨hzN, hzS⟩, hzV⟩
  exact ⟨w, hw.2, hwU, hwV⟩

end DifferentialGeometry.Topology
