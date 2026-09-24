/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingNonempty
import DifferentialGeometry.Topology.Connected.BicollarComplement

/-! # Section34Piercing Component Stability -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.isConnected_interior_three {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B : Set M} (h : IsPLCellOn 3 S B) :
    IsConnected (interior S) := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := h
  rw [← hu.image_interior]
  exact (isConnected_interior_of_isPLBall (show IsPLBall 3 P from ⟨r, hr⟩)).image u
    (hu.continuousOn.mono interior_subset)

theorem IsPLCellOn.frontier_inter_interior_nonempty {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B C : Set M}
    (h : IsPLCellOn 3 S B) (hC : IsClosed C) (hin : (S ∩ interior C).Nonempty)
    (hout : (S \ C).Nonempty) : (frontier C ∩ interior S).Nonempty := by
  obtain ⟨x, hxS, hxC⟩ := hin
  obtain ⟨y, hyS, hyC⟩ := hout
  obtain ⟨a, haC, haS⟩ := mem_closure_iff_nhds.mp (h.subset_closure_interior hxS) _
    (isOpen_interior.mem_nhds hxC)
  obtain ⟨b, hbC, hbS⟩ := mem_closure_iff_nhds.mp (h.subset_closure_interior hyS) _
    (hC.isOpen_compl.mem_nhds hyC)
  by_contra hne
  have hcover : interior S ⊆ interior C ∪ Cᶜ := by
    intro z hzS
    by_cases hzC : z ∈ C
    · refine Or.inl ?_
      by_contra hzi
      exact hne ⟨z, by rw [hC.frontier_eq]; exact ⟨hzC, hzi⟩, hzS⟩
    · exact Or.inr hzC
  have hsub := h.isConnected_interior_three.isPreconnected.subset_left_of_subset_union
    isOpen_interior hC.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover ⟨a, haS, haC⟩
  exact hbC (interior_subset (hsub hbS))

private theorem preconnectedSide {X : Type*} [TopologicalSpace X] {S P : Set X}
    (hS : IsPreconnected S) (hP : IsClosed P) (hSP : Disjoint S (frontier P)) :
    S ⊆ interior P ∨ Disjoint S P := by
  have hcover : S ⊆ interior P ∪ Pᶜ := by
    intro z hzS
    by_cases hzP : z ∈ P
    · refine Or.inl ?_
      by_contra hzi
      exact Set.disjoint_left.mp hSP hzS (by rw [hP.frontier_eq]; exact ⟨hzP, hzi⟩)
    · exact Or.inr hzP
  rcases hS.subset_or_subset isOpen_interior hP.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with h | h
  · exact Or.inl h
  · exact Or.inr (subset_compl_iff_disjoint_right.mp h)

theorem compact_connected_sides_of_component_pair {X : Type*} [TopologicalSpace X]
    {R P : Set X} (hR : IsCompact R) (hP : IsClosed P) (hRP : Disjoint R (frontier P))
    (hpair : ∃ a ∈ R, ∃ b ∈ R, ∀ x ∈ R,
      connectedComponentIn R x = connectedComponentIn R a ∨
      connectedComponentIn R x = connectedComponentIn R b)
    (hin : (R ∩ interior P).Nonempty) (hout : (R \ P).Nonempty) :
    ∃ K₀ K₁ : Set X, IsCompact K₀ ∧ IsConnected K₀ ∧ IsCompact K₁ ∧ IsConnected K₁ ∧
      K₀ ∪ K₁ = R ∧ K₀ ⊆ interior P ∧ Disjoint K₁ P := by
  obtain ⟨x, hxR, hxP⟩ := hin
  obtain ⟨y, hyR, hyP⟩ := hout
  have hdich (z : X) : connectedComponentIn R z ⊆ interior P ∨
      Disjoint (connectedComponentIn R z) P := by
    have hcover : connectedComponentIn R z ⊆ interior P ∪ Pᶜ := by
      intro v hv
      by_cases hvP : v ∈ P
      · refine Or.inl ?_
        by_contra hvi
        exact Set.disjoint_left.mp hRP (connectedComponentIn_subset R z hv)
          (by rw [hP.frontier_eq]; exact ⟨hvP, hvi⟩)
      · exact Or.inr hvP
    rcases isPreconnected_connectedComponentIn.subset_or_subset isOpen_interior
      hP.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hcover with h | h
    · exact Or.inl h
    · exact Or.inr (subset_compl_iff_disjoint_right.mp h)
  have hxside : connectedComponentIn R x ⊆ interior P :=
    (hdich x).resolve_right fun hdis =>
      Set.disjoint_left.mp hdis (mem_connectedComponentIn hxR) (interior_subset hxP)
  have hyside : Disjoint (connectedComponentIn R y) P :=
    (hdich y).resolve_left fun hsub =>
      hyP (interior_subset (hsub (mem_connectedComponentIn hyR)))
  have hne : connectedComponentIn R x ≠ connectedComponentIn R y := by
    intro heq
    exact Set.disjoint_left.mp hyside (heq ▸ mem_connectedComponentIn hxR)
      (interior_subset hxP)
  obtain ⟨a, ha, b, hb, hcomp⟩ := hpair
  have hcov : ∀ z ∈ R, connectedComponentIn R z = connectedComponentIn R x ∨
      connectedComponentIn R z = connectedComponentIn R y := by
    intro z hz
    rcases hcomp x hxR with hx | hx <;> rcases hcomp y hyR with hy | hy <;>
      rcases hcomp z hz with hz | hz <;> grind
  have hc (z : X) (hz : z ∈ R) : IsCompact (connectedComponentIn R z) := by
    let : CompactSpace R := isCompact_iff_compactSpace.mp hR
    rw [connectedComponentIn_eq_image hz]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  refine ⟨connectedComponentIn R x, connectedComponentIn R y, hc x hxR,
    isConnected_connectedComponentIn_iff.mpr hxR, hc y hyR,
    isConnected_connectedComponentIn_iff.mpr hyR, ?_, hxside, hyside⟩
  apply Subset.antisymm
    (union_subset (connectedComponentIn_subset R x) (connectedComponentIn_subset R y))
  intro z hz
  rcases hcov z hz with hzcomp | hzcomp
  · exact Or.inl (hzcomp ▸ mem_connectedComponentIn hz)
  · exact Or.inr (hzcomp ▸ mem_connectedComponentIn hz)

theorem exists_compact_connected_buffers_of_bicollar {X : Type*} [TopologicalSpace X]
    [T2Space X] {N S W R P : Set X} {ρ : X × ℝ → X} [LocallyConnectedSpace N]
    (hN : IsPreconnected N) (hS : IsConnected S) (hSc : IsCompact S) (hR : IsCompact R)
    (hRN : R ⊆ N \ S) (hcover : R ∪ W = N)
    (htrace : R ∩ W = ρ '' (S ×ˢ {(-1 : ℝ), 1})) (hW : W ∈ 𝓝ˢ[N] S)
    (hρ : ContinuousOn ρ (S ×ˢ Icc (-1 : ℝ) 1))
    (hbij : BijOn ρ (S ×ˢ Icc (-1 : ℝ) 1) W) (hzero : ∀ x ∈ S, ρ (x, 0) = x)
    (hP : IsClosed P) (hfrontier : N ∩ frontier P = S)
    (hin : (N ∩ interior P).Nonempty) (hout : (N \ P).Nonempty) :
    ∃ K₀ K₁ : Set X, IsCompact K₀ ∧ IsConnected K₀ ∧ IsCompact K₁ ∧ IsConnected K₁ ∧
      K₀ ⊆ N ∧ K₁ ⊆ N ∧ K₀ ∪ K₁ ∪ W = N ∧ K₀ ⊆ interior P ∧ Disjoint K₁ P := by
  have hSfr : S ⊆ frontier P := hfrontier.symm.subset.trans inter_subset_right
  have havoid : Disjoint (N \ S) (frontier P) :=
    Set.disjoint_left.mpr fun _ hx hxf => hx.2 (hfrontier.subset ⟨hx.1, hxf⟩)
  have hside (x : X) : connectedComponentIn (N \ S) x ⊆ interior P ∨
      Disjoint (connectedComponentIn (N \ S) x) P :=
    preconnectedSide isPreconnected_connectedComponentIn hP
      (havoid.mono_left (connectedComponentIn_subset _ _))
  have hinR : (R ∩ interior P).Nonempty := by
    obtain ⟨x, hxN, hxP⟩ := hin
    have hx : x ∈ N \ S := ⟨hxN, fun hxS => (hSfr hxS).2 hxP⟩
    obtain ⟨y, hyR, hxy⟩ :=
      Topology.exists_mem_complement_connectedComponentIn_of_bicollar
        hcover htrace hρ hbij hzero hx
    have hc : connectedComponentIn (N \ S) x ⊆ interior P :=
      (hside x).resolve_right fun hdis =>
        Set.disjoint_left.mp hdis (mem_connectedComponentIn hx) (interior_subset hxP)
    exact ⟨y, hyR, hc (hxy.symm ▸ mem_connectedComponentIn (hRN hyR))⟩
  have houtR : (R \ P).Nonempty := by
    obtain ⟨x, hxN, hxP⟩ := hout
    have hx : x ∈ N \ S := ⟨hxN, fun hxS => hxP (hP.frontier_subset (hSfr hxS))⟩
    obtain ⟨y, hyR, hxy⟩ :=
      Topology.exists_mem_complement_connectedComponentIn_of_bicollar
        hcover htrace hρ hbij hzero hx
    have hc : Disjoint (connectedComponentIn (N \ S) x) P :=
      (hside x).resolve_left fun hsub =>
        hxP (interior_subset (hsub (mem_connectedComponentIn hx)))
    exact ⟨y, hyR, Set.disjoint_left.mp hc
      (hxy.symm ▸ mem_connectedComponentIn (hRN hyR))⟩
  obtain ⟨K₀, K₁, hK₀, hc₀, hK₁, hc₁, hK, hi, ho⟩ :=
    compact_connected_sides_of_component_pair hR hP (havoid.mono_left hRN)
      (Topology.exists_connectedComponentIn_pair_complement_of_bicollar hN hS hSc
        hR.isClosed hcover htrace hW hρ hbij hzero) hinR houtR
  exact ⟨K₀, K₁, hK₀, hc₀, hK₁, hc₁,
    subset_union_left.trans (hK.subset.trans (hRN.trans sdiff_subset)),
    subset_union_right.trans (hK.subset.trans (hRN.trans sdiff_subset)),
    by rw [hK, hcover], hi, ho⟩

theorem piercing_components_of_connected_buffers {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {B K₀ K₁ R : Set X} {P T : Set Y} {G : X → Y}
    (hK₀ : IsConnected K₀) (hK₁ : IsConnected K₁) (hK₀B : K₀ ⊆ B) (hK₁B : K₁ ⊆ B)
    (hcover : B ⊆ K₀ ∪ K₁ ∪ R) (hG : ContinuousOn G B)
    (hinside : G '' K₀ ⊆ P) (houtside : Disjoint (G '' K₁) P) (hRT : G '' R ⊆ T) :
    (∃ y₀ ∈ G '' B ∩ P, ∀ z ∈ G '' B ∩ P, z ∉ T →
      z ∈ connectedComponentIn (G '' B ∩ P) y₀) ∧
    ∃ y₀ ∈ G '' B \ P, ∀ z ∈ G '' B \ P, z ∉ T →
      z ∈ connectedComponentIn (G '' B \ P) y₀ := by
  have hK₀image : G '' K₀ ⊆ G '' B ∩ P := subset_inter (image_mono hK₀B) hinside
  have hK₁image : G '' K₁ ⊆ G '' B \ P := fun y hy =>
    ⟨image_mono hK₁B hy, Set.disjoint_left.mp houtside hy⟩
  constructor
  · obtain ⟨x, hx⟩ := hK₀.nonempty
    refine ⟨G x, hK₀image (mem_image_of_mem G hx), ?_⟩
    intro z hz hzt
    obtain ⟨y, hy, rfl⟩ := hz.1
    have hyK : y ∈ K₀ := by
      rcases hcover hy with (hyK | hyK) | hyR
      · exact hyK
      · exact (Set.disjoint_left.mp houtside (mem_image_of_mem G hyK) hz.2).elim
      · exact (hzt (hRT (mem_image_of_mem G hyR))).elim
    exact ((hK₀.image G (hG.mono hK₀B)).isPreconnected.subset_connectedComponentIn
      (mem_image_of_mem G hx) hK₀image) (mem_image_of_mem G hyK)
  · obtain ⟨x, hx⟩ := hK₁.nonempty
    refine ⟨G x, hK₁image (mem_image_of_mem G hx), ?_⟩
    intro z hz hzt
    obtain ⟨y, hy, rfl⟩ := hz.1
    have hyK : y ∈ K₁ := by
      rcases hcover hy with (hyK | hyK) | hyR
      · exact (hz.2 (hinside (mem_image_of_mem G hyK))).elim
      · exact hyK
      · exact (hzt (hRT (mem_image_of_mem G hyR))).elim
    exact ((hK₁.image G (hG.mono hK₁B)).isPreconnected.subset_connectedComponentIn
      (mem_image_of_mem G hx) hK₁image) (mem_image_of_mem G hyK)

end DifferentialGeometry.Topology.PiecewiseLinear
