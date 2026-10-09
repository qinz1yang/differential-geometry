import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingDiskComponents

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.subset_or_disjoint_boundary_disk {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B D J Y : Set M} (hS : IsPLCellOn 3 S B) (hD : IsPLCellOn 2 D J)
    (hDB : D ⊆ B) (hY : IsPreconnected Y) (hYB : Y ⊆ B) (hYJ : Disjoint Y J) :
    Y ⊆ D ∨ Disjoint D Y := by
  obtain ⟨E, hE, hcover, hmeet⟩ := hS.exists_closed_boundary_disk_complement hD hDB
  have hdis : Y ∩ (D ∩ E) = ∅ := hmeet.symm ▸ hYJ.inter_eq
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hY D E hD.isCompact.isClosed hE
    (hcover.symm ▸ hYB) hdis with h | h
  · exact Or.inl h
  · exact Or.inr (disjoint_left.mpr fun x hxD hxY =>
      disjoint_left.mp hYJ hxY (hmeet ▸ ⟨hxD, h hxY⟩))

theorem IsPLCellOn.exists_strict_trace_subfamily_after_disk {M ι : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [Finite ι]
    {S B D : Set M} {J : ι → Set M} (hS : IsPLCellOn 3 S B) (i : ι)
    (hD : IsPLCellOn 2 D (J i)) (hDB : D ⊆ B)
    (hJ : ∀ j, IsConnected (J j)) (hJB : ∀ j, J j ⊆ B)
    (hclosed : ∀ j, IsClosed (J j)) (hdis : Pairwise fun j k => Disjoint (J j) (J k)) :
    ∃ I : Set ι, Nat.card I < Nat.card ι ∧
      ((⋃ j, J j) \ D) = ⋃ j : I, J j.1 ∧
      (∀ j : I, Disjoint D (J j.1)) ∧ IsClosed ((⋃ j, J j) \ D) := by
  let I : Set ι := {j | Disjoint D (J j)}
  have hi : i ∉ I := by
    intro hi
    obtain ⟨x, hx⟩ := (hJ i).nonempty
    exact disjoint_left.mp hi (hD.boundary_subset hx) hx
  have hcard : Nat.card I < Nat.card ι := Set.ncard_lt_card (fun h => hi (h ▸ mem_univ i))
  have htrace : ((⋃ j, J j) \ D) = ⋃ j : I, J j.1 := by
    ext x
    constructor
    · rintro ⟨hx, hxD⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      have hji : j ≠ i := fun hji => hxD (hD.boundary_subset (hji ▸ hxj))
      rcases hS.subset_or_disjoint_boundary_disk hD hDB (hJ j).isPreconnected (hJB j)
        (hdis hji) with hsub | hsep
      · exact (hxD (hsub hxj)).elim
      · exact mem_iUnion.mpr ⟨⟨j, hsep⟩, hxj⟩
    · intro hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact ⟨mem_iUnion.mpr ⟨j.1, hxj⟩, fun hxD => disjoint_left.mp j.2 hxD hxj⟩
  refine ⟨I, hcard, htrace, fun j => j.2, ?_⟩
  rw [htrace]
  exact isClosed_iUnion_of_finite fun j => hclosed j.1

end DifferentialGeometry.Topology.PiecewiseLinear
