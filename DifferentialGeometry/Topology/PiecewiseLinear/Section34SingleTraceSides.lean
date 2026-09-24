import DifferentialGeometry.Topology.PiecewiseLinear.Section34SingleCircleAnnulusComponents
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingSideConnectivity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem connected_sides_of_pair_cover {M : Type*} [TopologicalSpace M]
    {A X J L R : Set M} (hX : IsClosed X) (htrace : A ∩ frontier X = J)
    (hL : IsConnected L) (hR : IsConnected R) (hcover : L ∪ R = A \ J)
    (hpos : (A ∩ interior X).Nonempty) (hneg : (A \ X).Nonempty)
    (hattach : J ⊆ closure (A ∩ interior X)) :
    IsConnected (A ∩ X) ∧ IsConnected (A \ X) := by
  have hside (Y : Set M) (hY : IsConnected Y) (hYA : Y ⊆ A \ J) :
      Y ⊆ interior X ∨ Y ⊆ Xᶜ := by
    apply hY.isPreconnected.subset_or_subset isOpen_interior hX.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset)
    intro x hx
    by_cases hxX : x ∈ X
    · exact Or.inl ((mem_interior_iff_notMem_frontier hxX).mpr
        (fun hxfr => (hYA hx).2 (htrace.subset ⟨(hYA hx).1, hxfr⟩)))
    · exact Or.inr hxX
  have hLA : L ⊆ A \ J := subset_union_left.trans hcover.subset
  have hRA : R ⊆ A \ J := subset_union_right.trans hcover.subset
  have hposA : A ∩ interior X ⊆ A \ J := by
    rintro x ⟨hxA, hxX⟩
    exact ⟨hxA, fun hxJ => disjoint_left.mp disjoint_interior_frontier hxX
      (htrace.superset hxJ).2⟩
  have hnegA : A \ X ⊆ A \ J := by
    rintro x ⟨hxA, hxX⟩
    exact ⟨hxA, fun hxJ => hxX (hX.frontier_subset (htrace.superset hxJ).2)⟩
  have heq {Y Z : Set M} (hYZ : Y ∪ Z = A \ J)
      (hY : Y ⊆ interior X) (hZ : Z ⊆ Xᶜ) :
      A ∩ interior X = Y ∧ A \ X = Z := by
    constructor
    · apply Subset.antisymm
      · intro x hx
        rcases hYZ.superset (hposA hx) with hy | hz
        · exact hy
        · exact (hZ hz (interior_subset hx.2)).elim
      · exact fun _ hx => ⟨(hYZ.subset (Or.inl hx)).1, hY hx⟩
    · apply Subset.antisymm
      · intro x hx
        rcases hYZ.superset (hnegA hx) with hy | hz
        · exact (hx.2 (interior_subset (hY hy))).elim
        · exact hz
      · exact fun _ hx => ⟨(hYZ.subset (Or.inr hx)).1, hZ hx⟩
  have hboth : IsConnected (A ∩ interior X) ∧ IsConnected (A \ X) := by
    rcases hside L hL hLA with hLi | hLo <;> rcases hside R hR hRA with hRi | hRo
    · obtain ⟨x, hx⟩ := hneg
      rcases hcover.superset (hnegA hx) with hxL | hxR
      · exact (hx.2 (interior_subset (hLi hxL))).elim
      · exact (hx.2 (interior_subset (hRi hxR))).elim
    · obtain ⟨hp, hn⟩ := heq hcover hLi hRo
      exact ⟨hp.symm ▸ hL, hn.symm ▸ hR⟩
    · obtain ⟨hp, hn⟩ := heq ((union_comm R L).trans hcover) hRi hLo
      exact ⟨hp.symm ▸ hR, hn.symm ▸ hL⟩
    · obtain ⟨x, hx⟩ := hpos
      rcases hcover.superset (hposA hx) with hxL | hxR
      · exact (hLo hxL (interior_subset hx.2)).elim
      · exact (hRo hxR (interior_subset hx.2)).elim
  refine ⟨hboth.1.subset_closure (inter_subset_inter_right A interior_subset) ?_, hboth.2⟩
  rintro x ⟨hxA, hxX⟩
  by_cases hxi : x ∈ interior X
  · exact subset_closure ⟨hxA, hxi⟩
  · exact hattach (htrace.subset ⟨hxA, subset_closure hxX, hxi⟩)

theorem IsPLCellOn.isConnected_annulus_sides_of_single_circle {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ J X : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJA : J ⊆ A)
    (hends : Disjoint J (A₀ ∪ A₁)) (hX : IsClosed X) (htrace : A ∩ frontier X = J)
    (hpos : (A ∩ interior X).Nonempty) (hneg : (A \ X).Nonempty)
    (hattach : J ⊆ closure (A ∩ interior X)) :
    IsConnected (A ∩ X) ∧ IsConnected (A \ X) := by
  obtain ⟨L, R, hL, hR, hcover⟩ :=
    hS.exists_connected_pair_cover_annulus_sdiff_circle hA hAB hJ hJA hends
  exact connected_sides_of_pair_cover hX htrace hL hR hcover hpos hneg hattach

end DifferentialGeometry.Topology.PiecewiseLinear
