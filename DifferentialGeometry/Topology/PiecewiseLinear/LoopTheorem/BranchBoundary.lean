import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCarrier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

namespace NormalSingularSetTriangulation

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM : Set M}

open Classical in
private theorem branchComplex_boundary_vertex
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    {x : EuclideanSpace ℝ (Fin T.piece.ambientDim)}
    (hx : x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) 1
      (T.branchComplex c)).space) :
    ∃ v : (T.branchComplex c).vertices,
      (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) = x ∧
      ((SimplicialComplex.edgeGraph (T.branchComplex c)).neighborSet v).ncard = 1 := by
  let _ : Finite (T.branchComplex c).faces :=
    (T.branchComplex_faces_finite c).to_subtype
  obtain ⟨s, hs, hxs⟩ := (@boundaryComplex _ _ _ (Classical.decEq _) 1
    (T.branchComplex c)).mem_space_iff.mp hx
  have hsBoundary := hs
  obtain ⟨hsK, t, htK, hst, hcard, -⟩ := hs
  have hspos : 0 < s.card :=
    Finset.card_pos.mpr ((T.branchComplex c).nonempty_of_mem_faces hsK)
  have hscard : s.card = 1 := by
    have hle := Finset.card_le_card hst
    omega
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hscard
  have hxv : x = v := by
    simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hxs
  subst x
  let w : (T.branchComplex c).vertices := ⟨v, hsK⟩
  refine ⟨w, rfl, ?_⟩
  exact (mem_boundaryComplex_vertices_iff_edgeGraph_neighborSet_ncard_eq_one
    (T.branchComplex c) (T.branchComplex_isManifoldWithBoundary c) w).mp hsBoundary

open Classical in
private theorem complex_boundary_vertex
    (T : NormalSingularSetTriangulation D BdM)
    {x : EuclideanSpace ℝ (Fin T.piece.ambientDim)}
    (hx : x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) 1 T.complex).space) :
    ∃ v : T.complex.vertices,
      (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) = x ∧
      ((SimplicialComplex.edgeGraph T.complex).neighborSet v).ncard = 1 := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  obtain ⟨s, hs, hxs⟩ :=
    (@boundaryComplex _ _ _ (Classical.decEq _) 1 T.complex).mem_space_iff.mp hx
  have hsBoundary := hs
  obtain ⟨hsK, t, htK, hst, hcard, -⟩ := hs
  have hspos : 0 < s.card := Finset.card_pos.mpr (T.complex.nonempty_of_mem_faces hsK)
  have hscard : s.card = 1 := by
    have hle := Finset.card_le_card hst
    omega
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hscard
  have hxv : x = v := by
    simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hxs
  subst x
  let w : T.complex.vertices := ⟨v, hsK⟩
  refine ⟨w, rfl, ?_⟩
  exact (mem_boundaryComplex_vertices_iff_edgeGraph_neighborSet_ncard_eq_one
    T.complex T.isManifoldWithBoundary w).mp hsBoundary

open Classical in
theorem branchComplex_boundary_iff_map_mem_boundary
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    {x : EuclideanSpace ℝ (Fin T.piece.ambientDim)}
    (hx : x ∈ (T.branchComplex c).space) :
    x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) 1
      (T.branchComplex c)).space ↔
      T.piece.piece.map x ∈ BdM := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite (T.branchComplex c).faces :=
    (T.branchComplex_faces_finite c).to_subtype
  let dE : DecidableEq (EuclideanSpace ℝ (Fin T.piece.ambientDim)) := inferInstance
  have hboundaryComplex :
      @boundaryComplex _ _ _ (Classical.decEq _) 1 T.complex =
        @boundaryComplex _ _ _ dE 1 T.complex := by
    exact congrArg
      (fun d : DecidableEq (EuclideanSpace ℝ (Fin T.piece.ambientDim)) =>
        @boundaryComplex _ _ _ d 1 T.complex)
      (Subsingleton.elim _ _)
  have hmapBoundary : T.piece.piece.map ''
      (@boundaryComplex _ _ _ (Classical.decEq _) 1 T.complex).space =
        doublePointSet D D.domain ∩ BdM := by
    rw [hboundaryComplex]
    exact T.map_boundary
  constructor
  · intro hxboundary
    obtain ⟨v, hvx, hdegree⟩ := T.branchComplex_boundary_vertex c hxboundary
    let w : c.supp := (T.branchVertexEquiv c).symm v
    have hvw : T.branchVertex c w = v := (T.branchVertexEquiv c).apply_symm_apply v
    have hglobalDegree :
        ((SimplicialComplex.edgeGraph T.complex).neighborSet w.1).ncard = 1 := by
      rw [← T.branchEdgeGraph_neighborSet_ncard c w, hvw]
      exact hdegree
    have hglobalBoundary :
        (w.1 : EuclideanSpace ℝ (Fin T.piece.ambientDim)) ∈
          (@boundaryComplex _ _ _ (Classical.decEq _) 1 T.complex).space := by
      apply (@boundaryComplex _ _ _ (Classical.decEq _) 1 T.complex).vertices_subset_space
      exact (mem_boundaryComplex_vertices_iff_edgeGraph_neighborSet_ncard_eq_one
        T.complex T.isManifoldWithBoundary w.1).mpr hglobalDegree
    have himage : T.piece.piece.map w.1 ∈
        T.piece.piece.map ''
          (@boundaryComplex _ _ _ (Classical.decEq _) 1 T.complex).space :=
      ⟨w.1, hglobalBoundary, rfl⟩
    rw [hmapBoundary] at himage
    have hwx : (w.1 : EuclideanSpace ℝ (Fin T.piece.ambientDim)) = x := by
      exact congrArg Subtype.val hvw |>.trans hvx
    simpa only [hwx] using himage.2
  · intro hmap
    have hbranchManifold : IsCombinatorialManifoldWithBoundary 1 (T.branchComplex c) :=
      T.branchComplex_isManifoldWithBoundary c
    have hdouble : T.piece.piece.map x ∈ doublePointSet D D.domain :=
      T.branchCarrier_subset_doublePointSet c ⟨x, hx, rfl⟩
    have himage : T.piece.piece.map x ∈
        T.piece.piece.map ''
          (@boundaryComplex _ _ _ (Classical.decEq _) 1 T.complex).space := by
      rw [hmapBoundary]
      exact ⟨hdouble, hmap⟩
    obtain ⟨z, hzboundary, hzx⟩ := himage
    have hzcomplex : z ∈ T.complex.space := by
      obtain ⟨s, hs, hzs⟩ :=
        (@boundaryComplex _ _ _ (Classical.decEq _) 1 T.complex).mem_space_iff.mp
          hzboundary
      exact T.complex.convexHull_subset_space hs.1 hzs
    have hzpiece : z ∈ T.piece.piece.complex.space :=
      space_mono_of_faces_subset T.faces_subset hzcomplex
    have hxpiece : x ∈ T.piece.piece.complex.space :=
      T.branchComplex_space_subset_piece c hx
    have hzx' : z = x :=
      T.piece.piece.bijOn.injOn hzpiece hxpiece hzx
    subst z
    obtain ⟨v, hvx, hglobalDegree⟩ := T.complex_boundary_vertex hzboundary
    have hvbranch : (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) ∈
        (T.branchComplex c).vertices := by
      change {v.1} ∈ (T.branchComplex c).faces
      have hvglobal : (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) ∈
          T.complex.vertices := v.2
      have hxbranchface : {v.1} ∈ (T.branchComplex c).faces :=
        (SimplicialComplex.singleton_mem_subcomplex_iff_mem_space
          (K := T.complex) (L := T.branchComplex c)
          (T.branchComplex_faces_subset c) hvglobal).mpr (hvx ▸ hx)
      have hxvertices : (v : EuclideanSpace ℝ (Fin T.piece.ambientDim)) ∈
          T.branchVertices c := hxbranchface.2 (by simp)
      obtain ⟨u, huc, huv⟩ := hxvertices
      have huv' : u = v := Subtype.ext huv
      have hvsupp : v ∈ c.supp := huv' ▸ huc
      exact (T.branchVertex c ⟨v, hvsupp⟩).2
    let vb : (T.branchComplex c).vertices := ⟨v, hvbranch⟩
    let w : c.supp := (T.branchVertexEquiv c).symm vb
    have hvw : T.branchVertex c w = vb := (T.branchVertexEquiv c).apply_symm_apply vb
    have hwv : w.1 = v := by
      apply Subtype.ext
      exact congrArg
        (fun z : (T.branchComplex c).vertices =>
          (z : EuclideanSpace ℝ (Fin T.piece.ambientDim))) hvw
    have hbranchDegree :
        ((SimplicialComplex.edgeGraph (T.branchComplex c)).neighborSet vb).ncard = 1 := by
      rw [← hvw, T.branchEdgeGraph_neighborSet_ncard c w, hwv]
      exact hglobalDegree
    have hvboundary :=
      (mem_boundaryComplex_vertices_iff_edgeGraph_neighborSet_ncard_eq_one
        (T.branchComplex c) hbranchManifold vb).mpr hbranchDegree
    have hvbx : (vb : EuclideanSpace ℝ (Fin T.piece.ambientDim)) = x := by
      exact hvx
    rw [← hvbx]
    exact (@boundaryComplex _ _ _ (Classical.decEq _) 1
      (T.branchComplex c)).vertices_subset_space hvboundary

end NormalSingularSetTriangulation

end DifferentialGeometry.Topology.PiecewiseLinear
