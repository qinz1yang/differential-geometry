/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhoodExists
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSpanningTrees
import DifferentialGeometry.Topology.PiecewiseLinear.TwoComponentsOfPseudoCell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isConnected_compl_interior_of_isConnected_frontier {X : Type*} [TopologicalSpace X]
    [ConnectedSpace X] {F : Set X} (hF : IsConnected (frontier F)) :
    IsConnected (interior F)ᶜ := by
  have hZ : (interior F)ᶜ = Fᶜ ∪ frontier F := by
    rw [← closure_compl, closure_eq_self_union_frontier, frontier_compl]
  have hfrZ : frontier F ⊆ (interior F)ᶜ := fun x hx hxi => hx.2 hxi
  refine ⟨hF.nonempty.mono hfrZ, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hZuv hZdis
  have hkey : ∀ u v : Set X, IsClosed u → IsClosed v → (interior F)ᶜ ⊆ u ∪ v →
      (interior F)ᶜ ∩ (u ∩ v) = ∅ → frontier F ⊆ u → (interior F)ᶜ ⊆ u := by
    intro u v hu hv hZuv hZdis hfru
    have hQ : IsClopen ((interior F)ᶜ ∩ v) := by
      refine ⟨isOpen_interior.isClosed_compl.inter hv, ?_⟩
      rw [isOpen_iff_forall_mem_open]
      rintro y ⟨hyZ, hyv⟩
      have hyu : y ∉ u := fun hyu =>
        (Set.eq_empty_iff_forall_notMem.mp hZdis) y ⟨hyZ, hyu, hyv⟩
      have hyfr : y ∉ frontier F := fun hyfr => hyu (hfru hyfr)
      have hycl : y ∉ closure F := by
        intro hycl
        rw [hZ] at hyZ
        rcases hyZ with hyF | hyF
        · exact hyfr ⟨hycl, fun hyi => hyF (interior_subset hyi)⟩
        · exact hyfr hyF
      refine ⟨(closure F)ᶜ ∩ uᶜ, fun z hz => ?_, isClosed_closure.isOpen_compl.inter
        hu.isOpen_compl, hycl, hyu⟩
      have hzZ : z ∈ (interior F)ᶜ := fun hzi => hz.1 (subset_closure (interior_subset hzi))
      exact ⟨hzZ, (hZuv hzZ).resolve_left hz.2⟩
    rcases isClopen_iff.mp hQ with hQe | hQu
    · intro z hz
      by_contra hzu
      have hzv : z ∈ v := (hZuv hz).resolve_left hzu
      have hmem : z ∈ (interior F)ᶜ ∩ v := ⟨hz, hzv⟩
      rw [hQe] at hmem
      exact hmem
    · exfalso
      obtain ⟨y, hy⟩ := hF.nonempty
      have hyQ : y ∈ (interior F)ᶜ ∩ v := by
        rw [hQu]
        exact mem_univ y
      exact (Set.eq_empty_iff_forall_notMem.mp hZdis) y ⟨hfrZ hy, hfru hy, hyQ.2⟩
  have hfr := isPreconnected_iff_subset_of_disjoint_closed.mp hF.isPreconnected u v hu hv
    (hfrZ.trans hZuv) (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hy, hyuv⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hZdis) y ⟨hfrZ hy, hyuv⟩)
  rcases hfr with hfru | hfrv
  · exact Or.inl (hkey u v hu hv hZuv hZdis hfru)
  · refine Or.inr (hkey v u hv hu (fun z hz => (hZuv hz).symm) ?_ hfrv)
    rw [inter_comm v u]
    exact hZdis

section TubeFrontier

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3}

theorem IsTube.isConnected_frontier (ht : IsTube K N C D Dbd h N')
    (hconn : IsConnected K.space) : IsConnected (frontier N) := by
  classical
  have : Finite K.faces := ht.facesFinite.to_subtype
  let F : E3 → Set E3 := fun v => closure ((frontier (C v) ∩ frontier N) \
    ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ v ∈ f}, Dbd f)
  have hNc : IsClosed N := ht.isClosed
  have hFN : ∀ v, F v ⊆ frontier N := fun v =>
    closure_minimal (fun x hx => hx.1.2) isClosed_frontier
  have hcover : frontier N = ⋃ v : K.vertices, F v := by
    apply Subset.antisymm
    · intro x hx
      have hxN := hNc.frontier_subset hx
      rw [ht.unionEq] at hxN
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxN
      have hxfr : x ∈ frontier (C v) := ⟨subset_closure hxv, fun hxi =>
        hx.2 (interior_mono (ht.dualCell_subset hv) hxi)⟩
      exact mem_iUnion.mpr ⟨⟨v, hv⟩, ht.frontier_inter_frontier_subset_closure_freeFace hv
        ⟨hxfr, hx⟩⟩
    · exact iUnion_subset fun v => hFN v
  have hrim : ∀ f ∈ K.faces, f.card = 2 → ∀ a ∈ K.vertices, a ∈ f → Dbd f ⊆ F a := by
    intro f hf hfc a ha haf x hx
    have hxD : x ∈ D f := by
      rw [← ht.splitProper f hf hfc] at hx
      exact hx.1
    have hxN : x ∈ frontier N := by
      rw [← ht.splitProper f hf hfc] at hx
      exact hx.2
    exact ht.frontier_inter_frontier_subset_closure_freeFace ha
      ⟨ht.splitDisk_subset_frontier ha hf hfc haf hxD, hxN⟩
  have hrimne : ∀ f ∈ K.faces, f.card = 2 → (Dbd f).Nonempty := by
    intro f hf hfc
    obtain ⟨r, -, hrb⟩ := ht.splitCell f hf hfc
    rw [hrb]
    obtain ⟨p, hp⟩ := (isConnected_stdSimplexBoundary 0).nonempty
    exact ⟨r p, p, hp, rfl⟩
  obtain ⟨x₀, hx₀⟩ := hconn.nonempty
  obtain ⟨s₀, hs₀, -⟩ := K.mem_space_iff.mp hx₀
  obtain ⟨v₀, hv₀⟩ := K.nonempty_of_mem_faces hs₀
  have : Nonempty K.vertices :=
    ⟨⟨v₀, K.down_closed hs₀ (Finset.singleton_subset_iff.mpr hv₀) (Finset.singleton_nonempty v₀)⟩⟩
  have hgraph := edgeGraph_connected_of_isConnected_space K hconn
  have hstep : ∀ a b : K.vertices, (SimplicialComplex.edgeGraph K).Adj a b →
      (F a ∩ F b).Nonempty := by
    intro a b hab
    obtain ⟨hne, hmem⟩ := hab
    rw [classical_insert_singleton_eq_pair] at hmem
    have hab' : (a : E3) ≠ b := fun h => hne (Subtype.ext h)
    have hfc : ({(a : E3), (b : E3)} : Finset E3).card = 2 := Finset.card_pair hab'
    obtain ⟨y, hy⟩ := hrimne _ hmem hfc
    exact ⟨y, hrim _ hmem hfc a a.2 (Finset.mem_insert_self _ _) hy,
      hrim _ hmem hfc b b.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hy⟩
  rw [hcover]
  exact IsConnected.iUnion_of_reflTransGen (fun v => (ht.freeFaceConnected v v.2).closure)
    fun i j => Relation.ReflTransGen.mono hstep i j
      ((SimpleGraph.reachable_iff_reflTransGen i j).mp (hgraph.preconnected i j))

theorem IsTube.frontier_eq_image_frontier (ht : IsTube K N C D Dbd h N') :
    frontier N' = h '' frontier N := by
  have hNc := ht.isCompact
  have hN'c : IsCompact N' := by
    rw [ht.imageEq]
    exact hNc.image_of_continuousOn ht.continuousOn
  rw [hN'c.isClosed.frontier_eq, ht.interior_eq_image_interior, hNc.isClosed.frontier_eq,
    ht.imageEq]
  exact (ht.injOn.image_sdiff_subset interior_subset).symm

end TubeFrontier

section HandleComplement

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}

theorem IsHandleDecompositionOfTube.isConnected_compl_interior
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hconn : IsConnected K.space) : IsConnected (interior N')ᶜ := by
  have ht := hd.tube
  apply isConnected_compl_interior_of_isConnected_frontier
  rw [ht.frontier_eq_image_frontier]
  exact (ht.isConnected_frontier hconn).image h
    (ht.continuousOn.mono (ht.isClosed.frontier_subset))

end HandleComplement

end DifferentialGeometry.Topology.PiecewiseLinear
