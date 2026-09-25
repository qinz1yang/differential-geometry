import DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingRibbonContacts
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCornerCollarModel

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem section34_corner_base_subset_incident_spokes (a b : Bool) :
    section34CornerBase a b ⊆
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (if a then 0 else 2)) ∪
        segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (if b then 1 else 3)) := by
  rintro p (⟨hx, hy⟩ | ⟨hx, hy⟩)
  · left
    rw [mem_segment_zero_prod_iff]
    cases a
    · exact ⟨-p.1, by linarith [hx.2], by linarith [hx.1],
        by simp [fourSpokeModelLeaf], by simpa [fourSpokeModelLeaf] using hy⟩
    · exact ⟨p.1, hx.1, by linarith [hx.2], by simp [fourSpokeModelLeaf],
        by simpa [fourSpokeModelLeaf] using hy⟩
  · right
    rw [mem_segment_zero_prod_iff]
    cases b
    · exact ⟨-p.2, by linarith [hy.2], by linarith [hy.1],
        by simpa [fourSpokeModelLeaf] using hx, by simp [fourSpokeModelLeaf]⟩
    · exact ⟨p.2, hy.1, by linarith [hy.2], by simpa [fourSpokeModelLeaf] using hx,
        by simp [fourSpokeModelLeaf]⟩

theorem section34_corner_base_subset_frontier_of_target_contacts
    {E M : Type*} [TopologicalSpace E]
    {P R C : Set E} {u : E → M} (hu : InjOn u P) (hRP : R ⊆ P)
    (hfrontP : frontier R ⊆ P) {As Bs F D : Set M}
    (hfront : u '' frontier R = D ∪ F) (hF : As ∩ u '' R = F) (hD : Bs ∩ u '' R = D)
    {f : (ℝ × ℝ) × ℝ → E}
    (hfirst : u '' (f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) = u '' C ∩ As)
    (hsecond : u '' (f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) = u '' C ∩ Bs)
    (a b : Bool)
    (hquad : f '' (section34CrossingQuadrant a b ×ˢ Icc (0 : ℝ) 1) = C ∩ R) :
    f '' (section34CornerBase a b ×ˢ Icc (0 : ℝ) 1) ⊆ frontier R := by
  rintro x ⟨⟨p, s⟩, ⟨hp, hs⟩, rfl⟩
  have hxR := (hquad.subset
    ⟨(p, s), ⟨section34_corner_base_subset a b hp, hs⟩, rfl⟩).2
  have huDF : u (f (p, s)) ∈ D ∪ F := by
    rcases section34_corner_base_subset_incident_spokes a b hp with hx | hx
    · right
      apply hF.subset
      refine ⟨?_, mem_image_of_mem u hxR⟩
      apply (hfirst.subset ?_).2
      refine ⟨f (p, s), ⟨(p, s), ?_, rfl⟩, rfl⟩
      cases a
      · exact Or.inr ⟨hx, hs⟩
      · exact Or.inl ⟨hx, hs⟩
    · left
      apply hD.subset
      refine ⟨?_, mem_image_of_mem u hxR⟩
      apply (hsecond.subset ?_).2
      refine ⟨f (p, s), ⟨(p, s), ?_, rfl⟩, rfl⟩
      cases b
      · exact Or.inr ⟨hx, hs⟩
      · exact Or.inl ⟨hx, hs⟩
  obtain ⟨z, hz, heq⟩ := hfront.symm.subset huDF
  exact hu (hfrontP hz) (hRP hxR) heq ▸ hz

end DifferentialGeometry.Topology.PiecewiseLinear
