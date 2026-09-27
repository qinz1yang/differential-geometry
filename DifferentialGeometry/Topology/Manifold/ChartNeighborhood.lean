import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

open Set

namespace DifferentialGeometry.Topology

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]

theorem exists_compact_extChartAt_neighborhood (x : M) :
    ∃ (K : Set M) (U : Set E), IsCompact K ∧ IsOpen U ∧ x ∈ K ∧
      extChartAt I x x ∈ U ∧ K ⊆ (extChartAt I x).source ∧
      U ⊆ interior (extChartAt I x).target ∧ MapsTo (extChartAt I x).symm U K := by
  obtain ⟨C, hC, hxC, hCT⟩ :=
    exists_compact_subset (isOpen_extChartAt_target (I := I) x)
      (mem_extChartAt_target (I := I) x)
  refine ⟨(extChartAt I x).symm '' C, interior C,
    hC.image_of_continuousOn ((continuousOn_extChartAt_symm x).mono hCT),
    isOpen_interior, ?_, hxC, ?_, interior_mono hCT, ?_⟩
  · exact ⟨extChartAt I x x, interior_subset hxC, extChartAt_to_inv x⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (extChartAt I x).map_target (hCT hy)
  · intro y hy
    exact mem_image_of_mem _ (interior_subset hy)

end DifferentialGeometry.Topology
