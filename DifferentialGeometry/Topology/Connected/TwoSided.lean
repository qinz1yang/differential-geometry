import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.NhdsSet

open Set Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

def IsTwoSided (S : Set X) : Prop :=
  ∀ x ∈ S, ∃ V ∈ 𝓝ˢ (connectedComponentIn S x),
    ∀ W ∈ 𝓝ˢ (connectedComponentIn S x), W ⊆ V → IsConnected W →
      ¬IsPreconnected (W \ connectedComponentIn S x)

theorem not_isPreconnected_sdiff_of_inter_frontier_eq {N B W : Set X}
    (hN : closure (interior N) = N) (hB : B.Nonempty)
    (hBN : B ⊆ frontier N) (hW : W ∈ 𝓝ˢ B) (htrace : W ∩ frontier N = B) :
    ¬IsPreconnected (W \ B) := by
  have hclosed : IsClosed N := hN ▸ isClosed_closure
  obtain ⟨x, hxB⟩ := hB
  have hxW : W ∈ 𝓝 x := mem_nhdsSet_iff_forall.mp hW x hxB
  have hxN : x ∈ closure (interior N) := hN.symm ▸ hclosed.frontier_subset (hBN hxB)
  obtain ⟨y, hyW, hyN⟩ := (mem_closure_iff_nhds.mp hxN) W hxW
  have hxC : x ∈ closure Nᶜ := by
    rw [frontier_eq_closure_inter_closure] at hBN
    exact (hBN hxB).2
  obtain ⟨z, hzW, hzN⟩ := (mem_closure_iff_nhds.mp hxC) W hxW
  have hyB : y ∉ B := fun hy => (hBN hy).2 hyN
  have hzB : z ∉ B := fun hz => hzN (hclosed.frontier_subset (hBN hz))
  intro hconn
  have hcover : W \ B ⊆ interior N ∪ Nᶜ := by
    intro p hp
    by_cases hpN : p ∈ N
    · left
      by_contra hpint
      exact hp.2 (htrace ▸ ⟨hp.1, subset_closure hpN, hpint⟩)
    · exact Or.inr hpN
  obtain ⟨p, _, hpint, hpnot⟩ := hconn (interior N) Nᶜ isOpen_interior hclosed.isOpen_compl
    hcover ⟨y, ⟨hyW, hyB⟩, hyN⟩ ⟨z, ⟨hzW, hzB⟩, hzN⟩
  exact hpnot (interior_subset hpint)

theorem isTwoSided_frontier {N : Set X} (hN : closure (interior N) = N)
    [LocallyConnectedSpace (frontier N)] : IsTwoSided (frontier N) := by
  intro x hx
  let y : frontier N := ⟨x, hx⟩
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.mp
    (isOpen_connectedComponent (x := y))
  have hcomp : connectedComponentIn (frontier N) x = V ∩ frontier N := by
    rw [connectedComponentIn_eq_image hx, ← hVe]
    ext p
    simp [and_comm]
  have hCV : connectedComponentIn (frontier N) x ⊆ V :=
    hcomp ▸ inter_subset_left
  refine ⟨V, hV.mem_nhdsSet.mpr hCV, ?_⟩
  intro W hW hWV _
  apply not_isPreconnected_sdiff_of_inter_frontier_eq hN
    ⟨x, mem_connectedComponentIn hx⟩ (connectedComponentIn_subset _ _) hW
  apply Subset.antisymm
  · intro p hp
    rw [hcomp]
    exact ⟨hWV hp.1, hp.2⟩
  · intro p hp
    exact ⟨mem_of_mem_nhds (mem_nhdsSet_iff_forall.mp hW p hp),
      connectedComponentIn_subset _ _ hp⟩

theorem isTwoSided_frontier_of_isClosed_sdiff_connectedComponentIn {N : Set X}
    (hN : closure (interior N) = N)
    (hclosed : ∀ x ∈ frontier N, IsClosed (frontier N \ connectedComponentIn (frontier N) x)) :
    IsTwoSided (frontier N) := by
  intro x hx
  let C := connectedComponentIn (frontier N) x
  let V := (frontier N \ C)ᶜ
  have hCV : C ⊆ V := fun _ hp hbad => hbad.2 hp
  refine ⟨V, (hclosed x hx).isOpen_compl.mem_nhdsSet.mpr hCV, ?_⟩
  intro W hW hWV _
  apply not_isPreconnected_sdiff_of_inter_frontier_eq hN
    ⟨x, mem_connectedComponentIn hx⟩ (connectedComponentIn_subset _ _) hW
  apply Subset.antisymm
  · intro p hp
    by_contra hpC
    exact hWV hp.1 ⟨hp.2, hpC⟩
  · intro p hp
    exact ⟨mem_of_mem_nhds (mem_nhdsSet_iff_forall.mp hW p hp),
      connectedComponentIn_subset _ _ hp⟩
theorem IsTwoSided.of_union_components {S T : Set X} (hT : IsTwoSided T)
    (hST : S ⊆ T) (hcomponents : ∀ x ∈ S, connectedComponentIn T x ⊆ S) :
    IsTwoSided S := by
  intro x hx
  have heq : connectedComponentIn S x = connectedComponentIn T x :=
    Subset.antisymm (connectedComponentIn_mono x hST)
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (hST hx)) (hcomponents x hx))
  simpa only [heq] using hT x (hST hx)

theorem IsTwoSided.preimage_connectedComponentIn {Y : Type*} [TopologicalSpace Y]
    {f : X → Y} {S : Set Y} (h : IsTwoSided (f ⁻¹' S)) (hf : Continuous f) (p : Y) :
    IsTwoSided (f ⁻¹' connectedComponentIn S p) := by
  apply h.of_union_components (preimage_mono (connectedComponentIn_subset S p))
  intro x hx y hy
  have hxS : x ∈ f ⁻¹' S := connectedComponentIn_subset S p hx
  have hfy := connectedComponentIn_mono (f x) (image_preimage_subset f S)
    (hf.continuousOn.mapsTo_connectedComponentIn hxS hy)
  rwa [← connectedComponentIn_eq hx] at hfy
theorem isTwoSided_of_union_frontier_components {N S : Set X}
    (hN : closure (interior N) = N) [LocallyConnectedSpace (frontier N)]
    (hSN : S ⊆ frontier N)
    (hcomponents : ∀ x ∈ S, connectedComponentIn (frontier N) x ⊆ S) :
    IsTwoSided S :=
  (isTwoSided_frontier hN).of_union_components hSN hcomponents

end DifferentialGeometry.Topology
