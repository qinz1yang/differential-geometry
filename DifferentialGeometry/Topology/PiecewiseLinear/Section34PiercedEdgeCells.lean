import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundaryDiskFamilies

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_section34_pierced_edge_cells
    {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}
    {ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hends : ∀ e, src (.splitDisk e) =
      src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2))
    (e : Section34EdgeIndex 𝒦 𝒦') {O G : Set M}
    (hO : IsOpen O) (hDO : src (.splitDisk e) ⊆ O) (hG : IsCompact G)
    (hGC : G ⊆ interior (src (.vertexBall (ends e).1) ∪ src (.vertexBall (ends e).2))) :
    ∃ A B : Set M, IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ src (.splitDisk e) ∧ A ∩ B ⊆ O ∧
      A ∪ B ⊆ src (.vertexBall (ends e).1) ∪ src (.vertexBall (ends e).2) ∧
      G ⊆ interior A ∪ interior B ∧
      A \ O = src (.vertexBall (ends e).1) \ O ∧
      B \ O = src (.vertexBall (ends e).2) \ O := by
  have h₀ : IsPLCellOn 3 (src (.vertexBall (ends e).1)) (srcBd (.vertexBall (ends e).1)) :=
    hframe.2.2.2.1 (.vertexBall (ends e).1)
  have h₁ : IsPLCellOn 3 (src (.vertexBall (ends e).2)) (srcBd (.vertexBall (ends e).2)) :=
    hframe.2.2.2.1 (.vertexBall (ends e).2)
  have hD : IsPLCellOn 2 (src (.splitDisk e)) (srcBd (.splitDisk e)) :=
    hframe.2.2.2.1 (.splitDisk e)
  have hD₀ := section34_splitDisk_subset_vertex_boundary hframe hends (ends e).1 e (Or.inl rfl)
  have hD₁ := section34_splitDisk_subset_vertex_boundary hframe hends (ends e).2 e (Or.inr rfl)
  rw [h₀.boundary_eq_frontier] at hD₀
  rw [h₁.boundary_eq_frontier] at hD₁
  obtain ⟨A, B, hA, hB, hnonempty, hcircle, hmid, hlens, hAB, hcover, hAeq, hBeq⟩ :=
    exists_pierced_cell_pair_covering_compact h₀.isPolyhedralBall h₁.isPolyhedralBall
      (hends e ▸ hD.isPolyhedralBall) ((hends e).symm.subset.trans hD₀)
      ((hends e).symm.subset.trans hD₁) hO ((hends e).symm.subset.trans hDO) hG hGC
  exact ⟨A, B, hA, hB, hnonempty, hcircle, hmid.trans (hends e).symm.subset,
    hlens, hAB, hcover, hAeq, hBeq⟩

end DifferentialGeometry.Topology.PiecewiseLinear
