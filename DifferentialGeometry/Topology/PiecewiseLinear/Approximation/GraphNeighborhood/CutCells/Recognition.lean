import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphPatches
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RefinedResidualBalls
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.GraphNeighborhood.ResidualCells.Order
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphArcSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnPoints

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

theorem exists_graphCutCell_cell_boundaries
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) :
    ∃ B : Section34CutLabelOf 𝒦 𝒦' → Set M,
      ∀ l, IsPLCellOn (section34Dim l) (graphCutCell 𝒦 𝒦' l) (B l) := by
  classical
  have hall : ∀ l : Section34CutLabelOf 𝒦 𝒦',
      ∃ B, IsPLCellOn (section34Dim l) (graphCutCell 𝒦 𝒦' l) B := by
    intro l
    cases l with
    | vertexBall w =>
        exact ⟨_, isPLCellOn_graphVertexCell hsub hmap
          hK'.isCombinatorialManifoldWithBoundary w⟩
    | tetraBall t => exact exists_isPLCellOn_section34GraphResidualTetrahedron hsub hmap t
    | splitDisk e => exact ⟨_, isPLCellOn_graphSplittingDisk hK' e⟩
    | faceDisk s => exact exists_isPLCellOn_section34GraphResidualTriangle hsub hmap s
    | patch p =>
        simpa only [section34Dim, graphCutCell, inter_comm] using
          exists_isPLCellOn_section34GraphVertexCell_inter_residualTetrahedron
            hsub hmap p.1.1 p.1.2 p.2
    | faceArc a =>
        exact exists_isPLCellOn_section34GraphVertexCell_inter_residualTriangle
          hsub hmap a.1.1 a.1.2 a.2
    | edgeArc i =>
        simpa only [section34Dim, graphCutCell, inter_comm] using
          exists_isPLCellOn_section34GraphSplitCell_inter_residualTetrahedron
            hsub hmap i.1.1 i.1.2 i.2
    | markedPoint p =>
        obtain ⟨x, hx⟩ := exists_singleton_section34GraphSplitCell_inter_residualTriangle
          hsub hmap p.1.1 p.1.2 p.2
        have hxp : x ∈ graphSplittingDisk 𝒦 𝒦' p.1.2 ∩
            section34GraphResidualCell 𝒦 𝒦' p.1.1.1 := hx.symm ▸ mem_singleton x
        obtain ⟨y, hy, hxy⟩ := hxp.1
        refine ⟨∅, ?_⟩
        change IsPLCellOn 0 (graphSplittingDisk 𝒦 𝒦' p.1.2 ∩
          section34GraphResidualCell 𝒦 𝒦' p.1.1.1) ∅
        rw [hx, ← hxy]
        exact 𝒦'.isPLCellOn_singleton (splittingDisk_space_subset _ p.1.2.2.1 hy)
  choose B hB using hall
  exact ⟨B, hB⟩

theorem graphCutCell_subset_eq_or_dim_lt
    (hU : IsOpen U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (l m : Section34CutLabelOf 𝒦 𝒦')
    (h : graphCutCell 𝒦 𝒦' m ⊆ graphCutCell 𝒦 𝒦' l) :
    m = l ∨ section34Dim m < section34Dim l := by
  obtain ⟨hV, hE, hF, hP⟩ :=
    section34GraphCutFamily_subset_strict_on_recognized_sources hU hsub hmap hK'
  obtain ⟨hA, hI⟩ := section34GraphCutFamily_subset_strict_on_arcs hsub hmap
  cases m with
  | vertexBall w => exact hV w l h
  | tetraBall t =>
      exact Or.inl (graphCutCell_eq_of_tetrahedron_subset hsub hmap t l h)
  | splitDisk e => exact hE e l h
  | faceDisk s => exact hF s l h
  | patch p => exact section34GraphCutFamily_subset_strict_on_patches hsub hmap p l h
  | faceArc a => exact hA a l h
  | edgeArc i => exact hI i l h
  | markedPoint p => exact hP p l h

theorem isPLCellOn_graphMarkedPoint_proper_faces
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK' : IsCombinatorialManifold 3 𝒦'.complex) (p : Section34MarkIndex 𝒦 𝒦') :
    IsPLCellOn 0 (graphCutCell 𝒦 𝒦' (.markedPoint p))
      (⋃ m ∈ section34Face (graphCutCell 𝒦 𝒦') (.markedPoint p) \ {.markedPoint p},
        graphCutCell 𝒦 𝒦' m) := by
  obtain ⟨B, hB⟩ := exists_graphCutCell_cell_boundaries hsub hmap hK'
  have hem : (⋃ m ∈ section34Face (graphCutCell 𝒦 𝒦')
      (.markedPoint p) \ {.markedPoint p}, graphCutCell 𝒦 𝒦' m) = ∅ := by
    apply iUnion_eq_empty.mpr
    intro m
    apply iUnion_eq_empty.mpr
    intro hm
    have hd := (hB m).dim_le_of_subset (hB (.markedPoint p)) hm.1
    have hm0 : ∃ q, m = .markedPoint q := by
      cases m <;> simp_all [section34Dim]
    obtain ⟨q, rfl⟩ := hm0
    exact (hm.2 (congrArg Section34Label.markedPoint
      ((section34GraphMarkedPoint_subset_iff hsub hmap q p).mp hm.1))).elim
  rw [hem]
  exact (hB (.markedPoint p)).boundary_eq_empty ▸ hB (.markedPoint p)

end DifferentialGeometry.Topology.PiecewiseLinear
