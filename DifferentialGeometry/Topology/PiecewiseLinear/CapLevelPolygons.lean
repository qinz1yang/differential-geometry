import DifferentialGeometry.Topology.PiecewiseLinear.HeightCut

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem levelPolygons_union_of_fiber_inter_subset_singleton
    {A B : Set E} (hA : IsClosed A) (hB : IsClosed B) (f : E → ℝ) (r : ℝ) (p : E)
    (hinter : (A ∩ B) ∩ {x | f x = r} ⊆ {p}) :
    levelPolygons (A ∪ B) f r = levelPolygons A f r ∪ levelPolygons B f r := by
  apply levelPolygons_union_of_inter_eq hA hB f r rfl p
  intro T hT _ x hx
  exact hinter ⟨hx.2, (hT.2 hx.1).2⟩

theorem disjoint_levelPolygons_of_fiber_inter_subset_singleton
    {A B : Set E} {f : E → ℝ} {r : ℝ} {p : E}
    (hinter : (A ∩ B) ∩ {x | f x = r} ⊆ {p}) :
    Disjoint (levelPolygons A f r) (levelPolygons B f r) := by
  apply Set.disjoint_left.mpr
  intro T hTA hTB
  have hsub : T ⊆ {p} := by
    intro x hx
    exact hinter ⟨⟨(hTA.2 hx).1, (hTB.2 hx).1⟩, (hTA.2 hx).2⟩
  obtain ⟨x, hxT⟩ := hTA.1.nonempty
  obtain ⟨y, hyT, hyx⟩ := (hTA.1.isConnected_sdiff_singleton_one x).nonempty
  exact hyx ((hsub hyT).trans (hsub hxT).symm)

theorem encard_levelPolygons_union_of_fiber_inter_subset_singleton
    {A B : Set E} (hA : IsClosed A) (hB : IsClosed B) (f : E → ℝ) (r : ℝ) (p : E)
    (hinter : (A ∩ B) ∩ {x | f x = r} ⊆ {p}) :
    (levelPolygons (A ∪ B) f r).encard =
      (levelPolygons A f r).encard + (levelPolygons B f r).encard := by
  rw [levelPolygons_union_of_fiber_inter_subset_singleton hA hB f r p hinter]
  exact Set.encard_union_eq
    (disjoint_levelPolygons_of_fiber_inter_subset_singleton hinter)

theorem levelPolygons_union_cap_of_fiber_subset_singleton
    {A D : Set E} (hA : IsClosed A) (f : E → ℝ) (r : ℝ) (p : E)
    (hcap : D ∩ {x | f x = r} ⊆ {p}) :
    levelPolygons (A ∪ D) f r = levelPolygons A f r := by
  ext T
  constructor
  · intro hT
    have hsub : T \ {p} ⊆ A := by
      intro x hx
      obtain ⟨hxA | hxD, hxf⟩ := hT.2 hx.1
      · exact hxA
      · exact (hx.2 (hcap ⟨hxD, hxf⟩)).elim
    have hTA : T ⊆ A := (hT.1.closure_sdiff_singleton_one p).symm.subset.trans
      (closure_minimal hsub hA)
    exact ⟨hT.1, fun x hx => ⟨hTA hx, (hT.2 hx).2⟩⟩
  · intro hT
    exact ⟨hT.1, fun x hx => ⟨Or.inl (hT.2 hx).1, (hT.2 hx).2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
