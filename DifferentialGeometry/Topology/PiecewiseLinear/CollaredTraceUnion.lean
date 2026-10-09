/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteCollaredTrace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem traceCircles_eq_union_of_disjoint {L₁ L₂ T : Set E3}
    (h₁ : (traceCircles L₁ T).Finite) (h₂ : (traceCircles L₂ T).Finite)
    (hcover₁ : L₁ ∩ T = ⋃ G ∈ traceCircles L₁ T, G)
    (hcover₂ : L₂ ∩ T = ⋃ G ∈ traceCircles L₂ T, G) (hdis : Disjoint L₁ L₂) :
    traceCircles (L₁ ∪ L₂) T = traceCircles L₁ T ∪ traceCircles L₂ T := by
  classical
  let S := traceCircles L₁ T ∪ traceCircles L₂ T
  let _ : Finite S := (h₁.union h₂).to_subtype
  have hS : ∀ G : S, IsPLSphere 1 (G : Set E3) := by
    intro G
    rcases G.property with hG | hG
    · exact traceCircles_isPLSphere hG
    · exact traceCircles_isPLSphere hG
  have hpair : Pairwise fun G J : S => Disjoint (G : Set E3) (J : Set E3) := by
    intro G J hne
    have hne' : (G : Set E3) ≠ (J : Set E3) := fun he => hne (Subtype.ext he)
    rcases G.property with hG | hG <;> rcases J.property with hJ | hJ
    · exact pairwiseDisjoint_traceCircles L₁ T hG hJ hne'
    · exact hdis.mono ((traceCircles_subset hG).trans inter_subset_left)
        ((traceCircles_subset hJ).trans inter_subset_left)
    · exact hdis.symm.mono ((traceCircles_subset hG).trans inter_subset_left)
        ((traceCircles_subset hJ).trans inter_subset_left)
    · exact pairwiseDisjoint_traceCircles L₂ T hG hJ hne'
  have hcover : (L₁ ∪ L₂) ∩ T = ⋃ G : S, (G : Set E3) := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hx₁ | hx₂, hxT⟩
      · obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.mp (hcover₁.subset ⟨hx₁, hxT⟩)
        exact mem_iUnion.mpr ⟨⟨G, Or.inl hG⟩, hxG⟩
      · obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.mp (hcover₂.subset ⟨hx₂, hxT⟩)
        exact mem_iUnion.mpr ⟨⟨G, Or.inr hG⟩, hxG⟩
    · intro x hx
      obtain ⟨G, hxG⟩ := mem_iUnion.mp hx
      rcases G.property with hG | hG
      · obtain ⟨hxL, hxT⟩ := traceCircles_subset hG hxG
        exact ⟨Or.inl hxL, hxT⟩
      · obtain ⟨hxL, hxT⟩ := traceCircles_subset hG hxG
        exact ⟨Or.inr hxL, hxT⟩
  rw [traceCircles_eq_range_of_finite_circle_union hS hpair hcover]
  exact Subtype.range_coe_subtype

theorem HasFiniteCollaredTrace.union_of_disjoint {L₁ L₂ T : Set E3}
    (h₁ : HasFiniteCollaredTrace L₁ T) (h₂ : HasFiniteCollaredTrace L₂ T)
    (hdis : Disjoint L₁ L₂) : HasFiniteCollaredTrace (L₁ ∪ L₂) T := by
  have heq := traceCircles_eq_union_of_disjoint h₁.finiteTrace h₂.finiteTrace
    h₁.traceCover h₂.traceCover hdis
  refine ⟨h₁.isPolyhedron.union h₂.isPolyhedron, ?_, ?_, ?_⟩
  · rw [heq]
    exact h₁.finiteTrace.union h₂.finiteTrace
  · refine Subset.antisymm ?_ (iUnion₂_subset fun G hG => traceCircles_subset hG)
    rintro x ⟨hx₁ | hx₂, hxT⟩
    · obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.mp (h₁.traceCover.subset ⟨hx₁, hxT⟩)
      exact mem_iUnion₂.mpr ⟨G, heq.symm.subset (Or.inl hG), hxG⟩
    · obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.mp (h₂.traceCover.subset ⟨hx₂, hxT⟩)
      exact mem_iUnion₂.mpr ⟨G, heq.symm.subset (Or.inr hG), hxG⟩
  · intro G hG
    rcases heq.subset hG with hG | hG
    · apply (h₁.circleCollar G hG).of_locally_eq h₂.isPolyhedron.isClosed.isOpen_compl
        (fun x hx => disjoint_left.mp hdis ((traceCircles_subset hG hx).1))
      simp only [union_inter_distrib_right, inter_compl_self, union_empty]
    · apply (h₂.circleCollar G hG).of_locally_eq h₁.isPolyhedron.isClosed.isOpen_compl
        (fun x hx => disjoint_left.mp hdis.symm ((traceCircles_subset hG hx).1))
      simp only [union_inter_distrib_right, inter_compl_self, empty_union]

theorem HasFiniteCollaredTrace.of_disjoint_union_left {L₁ L₂ T : Set E3}
    (h : HasFiniteCollaredTrace (L₁ ∪ L₂) T) (hL₁ : IsPolyhedron L₁)
    (hL₂ : IsClosed L₂) (hdis : Disjoint L₁ L₂) : HasFiniteCollaredTrace L₁ T := by
  classical
  let S := {G ∈ traceCircles (L₁ ∪ L₂) T | G ⊆ L₁}
  have hSfin : S.Finite := h.finiteTrace.subset fun _ hG => hG.1
  let _ : Finite S := hSfin.to_subtype
  have hcover : L₁ ∩ T = ⋃ G : S, (G : Set E3) := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxL₁, hxT⟩
      obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.mp (h.traceCover.subset ⟨Or.inl hxL₁, hxT⟩)
      have hGL₁ : G ⊆ L₁ := by
        rcases isPreconnected_iff_subset_of_disjoint_closed.mp
            (traceCircles_isPLSphere hG).isConnected.isPreconnected L₁ L₂ hL₁.isClosed hL₂
            ((traceCircles_subset hG).trans inter_subset_left)
            (by rw [hdis.inter_eq, inter_empty]) with hsub | hsub
        · exact hsub
        · exact (disjoint_left.mp hdis hxL₁ (hsub hxG)).elim
      exact mem_iUnion.mpr ⟨⟨G, hG, hGL₁⟩, hxG⟩
    · intro x hx
      obtain ⟨G, hxG⟩ := mem_iUnion.mp hx
      exact ⟨G.property.2 hxG, (traceCircles_subset G.property.1 hxG).2⟩
  have hpair : Pairwise fun G J : S => Disjoint (G : Set E3) (J : Set E3) := by
    intro G J hne
    exact pairwiseDisjoint_traceCircles (L₁ ∪ L₂) T G.property.1 J.property.1
      (fun heq => hne (Subtype.ext heq))
  have heq : traceCircles L₁ T = S := by
    rw [traceCircles_eq_range_of_finite_circle_union
      (fun G : S => traceCircles_isPLSphere G.property.1) hpair hcover]
    exact Subtype.range_coe_subtype
  refine ⟨hL₁, heq.symm ▸ hSfin, ?_, ?_⟩
  · rw [heq]
    simpa only [iUnion_subtype] using hcover
  · intro G hG
    have hGS := heq.subset hG
    apply (h.circleCollar G hGS.1).of_locally_eq hL₂.isOpen_compl
      (fun x hx => disjoint_left.mp hdis (hGS.2 hx))
    simp only [union_inter_distrib_right, inter_compl_self, union_empty]

theorem HasFiniteCollaredTrace.of_disjoint_union_right {L₁ L₂ T : Set E3}
    (h : HasFiniteCollaredTrace (L₁ ∪ L₂) T) (hL₁ : IsClosed L₁)
    (hL₂ : IsPolyhedron L₂) (hdis : Disjoint L₁ L₂) : HasFiniteCollaredTrace L₂ T := by
  have h' : HasFiniteCollaredTrace (L₂ ∪ L₁) T := by rwa [union_comm]
  exact h'.of_disjoint_union_left hL₂ hL₁ hdis.symm
end DifferentialGeometry.Topology.PiecewiseLinear
