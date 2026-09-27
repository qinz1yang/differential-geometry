import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

open Set
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem OpenPartialHomeomorph.isOpen_extend_target_of_isInteriorPoint
    {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M)
    (hint : ∀ x ∈ e.source, I.IsInteriorPoint x) : IsOpen (e.extend I).target := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  have hx : (e.extend I).symm y ∈ e.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (e.extend I).map_target hy
  have hi := (I.isInteriorPoint_iff_of_mem_atlas (n := 1) (by simp) he hx).mp
    (hint _ hx)
  rw [(e.extend I).right_inv hy] at hi
  exact mem_interior_iff_mem_nhds.mp hi

theorem isOpen_extChartAt_target_of_boundarylessManifold [BoundarylessManifold I M] (x : M) :
    IsOpen (extChartAt I x).target :=
  OpenPartialHomeomorph.isOpen_extend_target_of_isInteriorPoint (chart_mem_atlas H x)
    (fun _ _ => BoundarylessManifold.isInteriorPoint)
