import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem ribbon_images_of_core_sides
    {E : Type*} [TopologicalSpace E] {G : (ℝ × ℝ) × ℝ → E} {C S X : Set E}
    {i j : Fin 4} (hS : G '' (section34MarkedRibbon i ∪ section34MarkedRibbon j) = C ∩ S)
    (haxis : MapsTo G section34MarkedAxis (frontier X)) (hX : IsClosed X)
    (hpos : G '' section34MarkedRibbonCore i ⊆ interior X)
    (hneg : G '' section34MarkedRibbonCore j ⊆ Xᶜ) :
    G '' section34MarkedRibbon i = (C ∩ S) ∩ X ∧
      G '' section34MarkedRibbon j = (C ∩ S) \ interior X := by
  constructor
  · apply Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      refine ⟨hS.subset ⟨p, Or.inl hp, rfl⟩, ?_⟩
      by_cases hp0 : p.1 = 0
      · exact hX.frontier_subset (haxis ⟨hp0, hp.2⟩)
      · exact interior_subset (hpos ⟨p, ⟨⟨hp.1, hp0⟩, hp.2⟩, rfl⟩)
    · rintro x ⟨hx, hxX⟩
      obtain ⟨p, hp, rfl⟩ := hS.symm.subset hx
      rcases hp with hp | hp
      · exact ⟨p, hp, rfl⟩
      · by_cases hp0 : p.1 = 0
        · exact ⟨p, section34_marked_axis_subset_ribbon i ⟨hp0, hp.2⟩, rfl⟩
        · exact (hneg ⟨p, ⟨⟨hp.1, hp0⟩, hp.2⟩, rfl⟩ hxX).elim
  · apply Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      refine ⟨hS.subset ⟨p, Or.inr hp, rfl⟩, ?_⟩
      by_cases hp0 : p.1 = 0
      · exact fun h => disjoint_left.mp disjoint_interior_frontier h (haxis ⟨hp0, hp.2⟩)
      · exact fun h => hneg ⟨p, ⟨⟨hp.1, hp0⟩, hp.2⟩, rfl⟩ (interior_subset h)
    · rintro x ⟨hx, hxX⟩
      obtain ⟨p, hp, rfl⟩ := hS.symm.subset hx
      rcases hp with hp | hp
      · by_cases hp0 : p.1 = 0
        · exact ⟨p, section34_marked_axis_subset_ribbon j ⟨hp0, hp.2⟩, rfl⟩
        · exact (hxX (hpos ⟨p, ⟨⟨hp.1, hp0⟩, hp.2⟩, rfl⟩)).elim
      · exact ⟨p, hp, rfl⟩

theorem HasPLCrossingAt.opposite_marked_cell_ribbon_images
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S X C : Set E}
    {G : (ℝ × ℝ) × ℝ → E} (hG : IsPLHomeomorphOn G spliceCylinder C) (i : Fin 4)
    (hS : G '' (section34MarkedRibbon i ∪ section34MarkedRibbon (i + 2)) = C ∩ S)
    (hF : G '' (section34MarkedRibbon (i + 1) ∪ section34MarkedRibbon (i + 3)) =
      C ∩ frontier X)
    (hc : G (0, 1 / 2) ∈ interior C)
    (hcross : HasPLCrossingAt S (frontier X) (G (0, 1 / 2)))
    (hball : ∀ N ∈ 𝓝 (G (0, 1 / 2)),
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
        0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
          MapsTo g (Metric.ball c r) (S ∩ N) ∧ g c = G (0, 1 / 2))
    (hX : IsClosed X) (hreg : closure (interior X) = X) :
    (G '' section34MarkedRibbon i = (C ∩ S) ∩ X ∧
      G '' section34MarkedRibbon (i + 2) = (C ∩ S) \ interior X) ∨
    (G '' section34MarkedRibbon i = (C ∩ S) \ interior X ∧
      G '' section34MarkedRibbon (i + 2) = (C ∩ S) ∩ X) := by
  have haxis : MapsTo G section34MarkedAxis (frontier X) := fun p hp =>
    (hF.subset ⟨p, Or.inl (section34_marked_axis_subset_ribbon (i + 1) hp), rfl⟩).2
  rcases hcross.opposite_marked_cell_ribbon_sides hG i hS hF hc hball hX hreg with h | h
  · exact Or.inl (ribbon_images_of_core_sides hS haxis hX h.1 h.2)
  · have hS' := (congrArg (fun Z => G '' Z) (union_comm _ _)).trans hS
    exact Or.inr (ribbon_images_of_core_sides hS' haxis hX h.2 h.1).symm

end DifferentialGeometry.Topology.PiecewiseLinear
