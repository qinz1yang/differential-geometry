import DifferentialGeometry.Topology.PlanarJordan.Regions

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

theorem outside_frontier_subset_compl_of_isCompact {C : Set Schoenflies.Plane}
    (hC : IsCompact C) (hJ : Schoenflies.IsJordanCurve (frontier C)) :
    Schoenflies.outside (frontier C) ⊆ Cᶜ := by
  have hsep := Schoenflies.jordan_curve_theorem hJ
  have hcover : Schoenflies.outside (frontier C) ⊆ interior C ∪ Cᶜ := by
    intro x hx
    by_cases hxC : x ∈ C
    · exact Or.inl ((mem_interior_iff_notMem_frontier hxC).mpr hx.1)
    · exact Or.inr hxC
  have hdisj : Disjoint (interior C) Cᶜ :=
    disjoint_compl_right.mono_left interior_subset
  have hsplit := IsPreconnected.subset_or_subset isOpen_interior hC.isClosed.isOpen_compl
    hdisj hcover hsep.isConnected_outside.isPreconnected
  exact hsplit.resolve_left fun h => hsep.not_isBounded_outside
    (hC.isBounded.subset (h.trans interior_subset))

theorem interior_eq_inside_frontier_of_isCompact {C : Set Schoenflies.Plane}
    (hC : IsCompact C) (hJ : Schoenflies.IsJordanCurve (frontier C))
    (hne : (interior C).Nonempty) : interior C = Schoenflies.inside (frontier C) := by
  have hsep := Schoenflies.jordan_curve_theorem hJ
  have hout := outside_frontier_subset_compl_of_isCompact hC hJ
  have hsub : interior C ⊆ Schoenflies.inside (frontier C) := by
    intro x hx
    have hxnot : x ∉ frontier C := fun h => h.2 hx
    have hxcover : x ∈ Schoenflies.inside (frontier C) ∪ Schoenflies.outside (frontier C) := by
      rw [Schoenflies.inside_union_outside]
      exact hxnot
    exact hxcover.resolve_right fun h => hout h (interior_subset hx)
  have hcover : Schoenflies.inside (frontier C) ⊆ interior C ∪ Cᶜ := by
    intro x hx
    by_cases hxC : x ∈ C
    · exact Or.inl ((mem_interior_iff_notMem_frontier hxC).mpr hx.1)
    · exact Or.inr hxC
  obtain ⟨p, hp⟩ := hne
  exact Subset.antisymm hsub
    (hsep.isConnected_inside.isPreconnected.subset_left_of_subset_union isOpen_interior
      hC.isClosed.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hcover
      ⟨p, hsub hp, hp⟩)

theorem closure_inside_frontier_eq_of_isCompact {C : Set Schoenflies.Plane}
    (hC : IsCompact C) (hJ : Schoenflies.IsJordanCurve (frontier C))
    (hne : (interior C).Nonempty) : closure (Schoenflies.inside (frontier C)) = C := by
  have hi := interior_eq_inside_frontier_of_isCompact hC hJ hne
  have hsep := Schoenflies.jordan_curve_theorem hJ
  rw [(Schoenflies.IsRegionOf.inside (frontier C)).closure_eq hsep, ← hi]
  exact (closure_eq_interior_union_frontier C).symm.trans hC.isClosed.closure_eq

end DifferentialGeometry.Topology.PlanarJordan
