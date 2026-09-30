import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryBall
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_isSubdivision_boundary_subcomplex_in_ball_neighborhoods {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1)))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPolyhedron P)
    (hPK : P ⊆ frontier K.space) :
    ∃ R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 1))),
      IsSubdivision R K ∧ R.faces.Finite ∧ (restrict R P).space = P ∧
      ∀ s ∈ (restrict R P).faces,
        ∃ C U : Set (EuclideanSpace ℝ (Fin (n + 1))),
          IsPLBall (n + 1) C ∧ C ⊆ K.space ∧ IsPLBall n (C ∩ frontier K.space) ∧
          IsOpen U ∧ (⋃ v ∈ s, closedStar R v) ⊆ U ∧ U ∩ K.space ⊆ C := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (n + 1))) := Classical.decEq _
  have hfront := frontier_space_eq_boundaryComplex_space hK
  have hclosed : IsClosed K.space := (isPolyhedron_space K).isClosed
  have hpatch (z : P) : ∃ C U : Set (EuclideanSpace ℝ (Fin (n + 1))),
      IsPLBall (n + 1) C ∧ C ⊆ K.space ∧ IsPLBall n (C ∩ frontier K.space) ∧
        IsOpen U ∧ (z : EuclideanSpace ℝ (Fin (n + 1))) ∈ U ∧ U ∩ K.space ⊆ C := by
    obtain ⟨C, hC, hCK, hCn, hCB⟩ :=
      exists_isPLBall_subset_inter_boundary K hK z (hfront ▸ hPK z.property)
    obtain ⟨V, hV, hVC⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hCn
    obtain ⟨U, hUV, hU, hzU⟩ := mem_nhds_iff.mp hV
    refine ⟨C, U, hC, hCK, ?_, hU, hzU, ?_⟩
    · rwa [hfront]
    · exact (inter_subset_inter_left K.space hUV).trans hVC
  choose C U hC hCK hCB hU hzU hUC using hpatch
  let V : Option P → Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    fun i => match i with
      | none => Pᶜ
      | some z => U z
  have hVo : ∀ i, IsOpen (((↑) : K.space → EuclideanSpace ℝ (Fin (n + 1))) ⁻¹' V i) := by
    intro i
    cases i with
    | none => exact hP.isClosed.isOpen_compl.preimage continuous_subtype_val
    | some z => exact (hU z).preimage continuous_subtype_val
  have hcover : K.space ⊆ ⋃ i, V i := by
    intro x _
    by_cases hxP : x ∈ P
    · exact mem_iUnion.mpr ⟨some ⟨x, hxP⟩, hzU ⟨x, hxP⟩⟩
    · exact mem_iUnion.mpr ⟨none, hxP⟩
  obtain ⟨R, hR, hRfin, hRP, hstars⟩ :=
    exists_isSubdivision_subcomplexes_closedStars_subset_cover K (fun _ : Unit => P)
      (fun _ => hP) (fun _ => hPK.trans hclosed.frontier_subset) V hVo hcover
  refine ⟨R, hR, hRfin, hRP (), ?_⟩
  intro s hs
  obtain ⟨i, hi⟩ := hstars s hs.1
  cases i with
  | none =>
      obtain ⟨v, hv⟩ := R.nonempty_of_mem_faces hs.1
      have hvS : v ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
        subset_convexHull ℝ _ hv
      have hvstar : v ∈ closedStar R v := mem_iUnion₂.mpr ⟨s, ⟨hs.1, hvS⟩, hvS⟩
      exact False.elim (hi (mem_iUnion₂.mpr ⟨v, hv, hvstar⟩) (hs.2 hvS))
  | some z => exact ⟨C z, U z, hC z, hCK z, hCB z, hU z, hi, hUC z⟩

open Classical in
theorem exists_isSubdivision_boundary_ball_stars {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 2)))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    {P : Set (EuclideanSpace ℝ (Fin (n + 2)))} (hP : IsPLBall (n + 1) P)
    (hPK : P ⊆ frontier K.space) :
    ∃ R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (n + 2))),
      IsSubdivision R K ∧ R.faces.Finite ∧ (restrict R P).space = P ∧
      ∀ s ∈ (restrict R P).faces,
        ∃ C : Set (EuclideanSpace ℝ (Fin (n + 2))),
          IsPLBall (n + 2) C ∧ C ⊆ K.space ∧
          C ∩ frontier K.space = (faceStarComplex (restrict R P) s).space ∧
          (faceStarComplex (restrict R P) s).space ⊆ frontier C := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin (n + 2))) := Classical.decEq _
  obtain ⟨R, hR, hRfin, hRP, hlocal⟩ :=
    exists_isSubdivision_boundary_subcomplex_in_ball_neighborhoods K hK hP.isPolyhedron hPK
  let _ : Finite R.faces := hRfin.to_subtype
  let A := restrict R P
  let _ : Finite A.faces := (restrict_faces_finite R P).to_subtype
  have hA : IsPLBall (n + 1) A.space := hRP.symm ▸ hP
  refine ⟨R, hR, hRfin, hRP, ?_⟩
  intro s hs
  obtain ⟨C, U, hC, hCK, -, -, hstars, hUC⟩ := hlocal s hs
  have hS : IsPLBall (n + 1) (faceStarComplex A s).space :=
    hA.isCombinatorialManifoldWithBoundary.isPLBall_faceStarComplex A hs
  have hSP : (faceStarComplex A s).space ⊆ P :=
    (space_mono_of_faces_subset (faceStarComplex_faces_subset A s)).trans hRP.le
  have hSC : (faceStarComplex A s).space ⊆ C := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := (faceStarComplex A s).mem_space_iff.mp hx
    obtain ⟨v, hv⟩ := A.nonempty_of_mem_faces hs
    have hxus : x ∈ convexHull ℝ ((u ∪ s : Finset _) : Set _) :=
      convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left) hxu
    have hvus : v ∈ convexHull ℝ ((u ∪ s : Finset _) : Set _) :=
      subset_convexHull ℝ _ (Finset.mem_union_right u hv)
    have hxstar : x ∈ closedStar R v := mem_iUnion₂.mpr ⟨u ∪ s, ⟨hu.2.1, hvus⟩, hxus⟩
    exact hUC ⟨hstars (mem_iUnion₂.mpr ⟨v, hv, hxstar⟩),
      hR.space_eq ▸ closedStar_subset_space R v hxstar⟩
  exact exists_isPLBall_inter_frontier_eq_of_subset (by simp) hC hCK hS hSC (hSP.trans hPK)

end DifferentialGeometry.Topology.PiecewiseLinear
