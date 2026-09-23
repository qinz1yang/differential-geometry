import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeGraphRegions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedEdgeCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedPiercedCells

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

theorem exists_section34_marked_graph_covering_edge_cells
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
    (p : Section34VertexIndex 𝒦 𝒦' → M) (hpinj : Function.Injective p)
    (hp : ∀ w, p w ∈ src (.vertexBall w))
    (hpg : ∀ w, p w ∈ graphSkeletonSpace 𝒦)
    (hne : ∀ e, (ends e).1 ≠ (ends e).2)
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
      p (ends e).1 ∉ B ∧ p (ends e).2 ∉ A ∧
      ∃ (D : Set M) (φ₀ φ₁ : M ≃ M), IsCompact D ∧ D ⊆ V ∧
        IsPLHomeomorphInto 3 φ₀ (src (.vertexBall (ends e).1)) ∧
        IsPLHomeomorphInto 3 φ₁ (src (.vertexBall (ends e).2)) ∧
        φ₀ '' src (.vertexBall (ends e).1) = A ∧ φ₁ '' src (.vertexBall (ends e).2) = B ∧
        EqOn φ₀ id Dᶜ ∧ EqOn φ₁ id Dᶜ := by
  obtain ⟨V, G, hV, hDV, hVO, hG, -, hGP, hGV, hforeign⟩ :=
    exists_section34_compact_edge_graph_region hU hframe hN ends (fun e => (hends e).1)
      e hO hDO
  have h₀ : IsPLCellOn 3 (src (.vertexBall (ends e).1)) (srcBd (.vertexBall (ends e).1)) :=
    hframe.2.2.2.1 (.vertexBall (ends e).1)
  have h₁ : IsPLCellOn 3 (src (.vertexBall (ends e).2)) (srcBd (.vertexBall (ends e).2)) :=
    hframe.2.2.2.1 (.vertexBall (ends e).2)
  have hD : IsPLCellOn 2 (src (.splitDisk e)) (srcBd (.splitDisk e)) :=
    hframe.2.2.2.1 (.splitDisk e)
  have hD₀ := section34_splitDisk_subset_vertex_boundary hframe
    (fun e => (hends e).2) (ends e).1 e (Or.inl rfl)
  have hD₁ := section34_splitDisk_subset_vertex_boundary hframe
    (fun e => (hends e).2) (ends e).2 e (Or.inr rfl)
  rw [h₀.boundary_eq_frontier] at hD₀
  rw [h₁.boundary_eq_frontier] at hD₁
  have hpI (w) (hw : p w ∈ src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2)) :
      p w ∈ interior (src (.vertexBall (ends e).1) ∪ src (.vertexBall (ends e).2)) :=
    hGP (hGV ⟨hpg w, hDV ((hends e).2.symm.subset hw)⟩)
  obtain ⟨A, B, hA, hB, -, hn₀, -, hn₁, hn, hs, hm, hl, hu, hc, hdA, hdB, hmaps⟩ :=
    exists_pierced_cell_pair_excluding_opposite_markers h₀.isPolyhedralBall h₁.isPolyhedralBall
      ((hends e).2 ▸ hD.isPolyhedralBall) ((hends e).2.symm.subset.trans hD₀)
      ((hends e).2.symm.subset.trans hD₁) hV ((hends e).2.symm.subset.trans hDV) hG hGP
      (hp _) (hp _) (hpI _) (hpI _) (fun he => hne e (hpinj he))
  exact ⟨V, A, B, hV, hDV, hVO, hforeign, hA, hB, hn, hs,
    hm.trans (hends e).2.symm.subset, hl, hu, hGV.trans hc, hdA, hdB, hn₀, hn₁, hmaps⟩

end DifferentialGeometry.Topology.PiecewiseLinear
