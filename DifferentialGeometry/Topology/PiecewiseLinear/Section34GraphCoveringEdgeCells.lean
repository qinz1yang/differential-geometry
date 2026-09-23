import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeGraphRegions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedEdgeCells

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_section34_graph_covering_edge_cells
    {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}
    (hU : IsOpen U) (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3)
      (section34CutNeighborhood src) (graphSkeletonSpace 𝒦) U)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea) ∧
      src (.splitDisk e) = src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2))
    (e : Section34EdgeIndex 𝒦 𝒦') {O : Set M} (hO : IsOpen O)
    (hDO : src (.splitDisk e) ⊆ O) :
    ∃ V A B : Set M, IsOpen V ∧ src (.splitDisk e) ⊆ V ∧ V ⊆ O ∩ U ∧
      (∀ w, w ≠ (ends e).1 → w ≠ (ends e).2 → Disjoint V (src (.vertexBall w))) ∧
      IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ src (.splitDisk e) ∧ A ∩ B ⊆ V ∧
      A ∪ B ⊆ src (.vertexBall (ends e).1) ∪ src (.vertexBall (ends e).2) ∧
      graphSkeletonSpace 𝒦 ∩ V ⊆ interior A ∪ interior B ∧
      A \ V = src (.vertexBall (ends e).1) \ V ∧
      B \ V = src (.vertexBall (ends e).2) \ V ∧
      ∃ (D : Set M) (φ₀ φ₁ : M ≃ M), IsCompact D ∧ D ⊆ V ∧
        IsPLHomeomorphInto 3 φ₀ (src (.vertexBall (ends e).1)) ∧
        IsPLHomeomorphInto 3 φ₁ (src (.vertexBall (ends e).2)) ∧
        φ₀ '' src (.vertexBall (ends e).1) = A ∧ φ₁ '' src (.vertexBall (ends e).2) = B ∧
        EqOn φ₀ id Dᶜ ∧ EqOn φ₁ id Dᶜ := by
  obtain ⟨V, G, hV, hDV, hVO, hG, -, hGP, hGV, hforeign⟩ :=
    exists_section34_compact_edge_graph_region hU hframe hN ends (fun e => (hends e).1)
      e hO hDO
  obtain ⟨A, B, hA, hB, hn, hs, hm, hl, hu, hc, hdA, hdB, hmaps⟩ :=
    exists_section34_pierced_edge_cells hframe (fun e => (hends e).2) e hV hDV hG hGP
  exact ⟨V, A, B, hV, hDV, hVO, hforeign, hA, hB, hn, hs, hm, hl, hu,
    hGV.trans hc, hdA, hdB, hmaps⟩

end DifferentialGeometry.Topology.PiecewiseLinear
