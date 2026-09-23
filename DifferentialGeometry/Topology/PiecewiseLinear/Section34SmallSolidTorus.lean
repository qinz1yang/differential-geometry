import DifferentialGeometry.Topology.PiecewiseLinear.Section34SmallRegularNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodSolidTorus

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLDerivedNeighborhoodExhaustion.exists_solidTorus_regularNeighborhood_subset_open
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O D : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C)
    (hD : IsPolyhedralBall (n := 3) 3 D) (hDU : D ⊆ U) (hCD : C ⊆ interior D)
    (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ S : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsTopologicalSolidTorus S ∧ S ⊆ O ∩ interior D := by
  classical
  obtain ⟨m, T, A, -, hcover, hfin, -, -, hman, -, hmono, -⟩ := h
  let _ : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  have hCU : C ⊆ U := hCD.trans (interior_subset.trans hDU)
  let Q := T.complex.space ∩ T.map ⁻¹' C
  have hQ : IsPLSphere 1 Q :=
    T.isPLSphere_preimage_of_isPolyhedralSphere A hcover hfin hmono hC hCU
  let P := T.complex.space ∩ T.map ⁻¹' D
  have hP : IsPLBall 3 P :=
    T.isPLBall_preimage_of_isPolyhedralBall A hcover hfin hmono hD hDU
  have hQP : Q ⊆ P := inter_subset_inter_right _ (preimage_mono (hCD.trans interior_subset))
  obtain ⟨R, hR, hnew, hRP, hRQ⟩ := T.exists_isSubdivision_restrict_pair_finite_change
    A hcover hfin hmono hP.isPolyhedron inter_subset_left hQ.isPolyhedron inter_subset_left
  let T₁ := T.subdivide R hR
    (T.locallyFinite_of_isSubdivision_of_finite_new_faces hR hnew)
  have hcardT : ∀ s ∈ T.complex.faces, s.card ≤ 3 + 1 := by
    intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ▸ hs)
    have : Finite (A i).faces := (hfin i).to_subtype
    exact (hman i).card_le (A i) hi
  have hCc : IsCompact C := by
    obtain ⟨P, -⟩ := hC
    rw [← P.piece.bijOn.image_eq]
    exact P.piece.isPolyhedron_space.isCompact.image_of_continuousOn P.piece.continuousOn
  let W : Bool → Set X := fun b => if b then O ∩ interior D else Cᶜ
  have hW : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact hCc.isClosed.isOpen_compl
    · exact hO.inter isOpen_interior
  have hUW : U ⊆ ⋃ b, W b := by
    intro x _
    by_cases hxC : x ∈ C
    · exact mem_iUnion.mpr ⟨true, hCO hxC, hCD hxC⟩
    · exact mem_iUnion.mpr ⟨false, hxC⟩
  obtain ⟨S, hS, hSLF, hstar⟩ := T₁.exists_isSubdivision_forall_image_subset
    (fun s hs => hR.card_le hcardT hs) W hW hUW
  have hST : IsSubdivision S T.complex := hS.trans hR
  let T₂ := T.subdivide S hST hSLF
  let G := restrict S Q
  have hGspace : G.space = Q := by
    have he := (hS.restrict (restrict R Q) (restrict_faces_subset R Q)).space_eq
    rwa [hRQ] at he
  have hQS : Q ⊆ S.space := inter_subset_left.trans hST.space_eq.symm.subset
  have hGfin : G.faces.Finite := by
    apply (T₂.finite_faces_inter_of_isCompact hQ.isPolyhedron.isCompact hQS).subset
    rintro s ⟨hs, hsc⟩
    have hx : s.centroid ℝ id ∈ convexHull ℝ (s : Set _) :=
      s.centroid_mem_convexHull (S.nonempty_of_mem_faces hs)
    exact ⟨hs, s.centroid ℝ id, hx, hsc hx⟩
  have : Finite G.faces := hGfin.to_subtype
  have hG : IsPLSphere 1 G.space := hGspace.symm ▸ hQ
  have hcardG : ∀ s ∈ G.faces, s.card ≤ 2 := fun s hs => card_le_of_isPLSphere G hG hs
  have hreg := T.isLocallyFiniteRegularNeighborhoodOf_locallyFinite_subdivision
    hU A hcover hfin hmono hman S hST hSLF G (restrict_faces_subset S Q) hcardG
  have himage : T.map '' G.space = C := by
    rw [hGspace]
    change T.map '' (T.complex.space ∩ T.map ⁻¹' C) = C
    rw [image_inter_preimage, T.bijOn.image_eq, inter_eq_right.mpr hCU]
  have hsmall : T.map '' (derivedNeighborhood S G).space ⊆ O ∩ interior D := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨s, hs, ⟨y, hys, hyG⟩, hzs⟩ := exists_face_meets_of_mem_derivedNeighborhood_space hz
    obtain ⟨b, hb⟩ := hstar s hs
    obtain ⟨v, hv⟩ := S.nonempty_of_mem_faces hs
    have hyW := hb v hv s hs hv (mem_image_of_mem T.map hys)
    have hzW := hb v hv s hs hv (mem_image_of_mem T.map hzs)
    cases b
    · exact (hyW ((hGspace.subset hyG).2)).elim
    · exact hzW
  let B := restrict S P
  have hBspace : B.space = P := by
    have he := (hS.restrict (restrict R P) (restrict_faces_subset R P)).space_eq
    rwa [hRP] at he
  have hPS : P ⊆ S.space := inter_subset_left.trans hST.space_eq.symm.subset
  have hBfin : B.faces.Finite := by
    apply (T₂.finite_faces_inter_of_isCompact hP.isPolyhedron.isCompact hPS).subset
    rintro s ⟨hs, hsc⟩
    have hx : s.centroid ℝ id ∈ convexHull ℝ (s : Set _) :=
      s.centroid_mem_convexHull (S.nonempty_of_mem_faces hs)
    exact ⟨hs, s.centroid ℝ id, hx, hsc hx⟩
  have : Finite B.faces := hBfin.to_subtype
  have hBball : IsPLBall 3 B.space := hBspace.symm ▸ hP
  have hGB : G.faces ⊆ B.faces := fun _ hs => ⟨hs.1, hs.2.trans hQP⟩
  have hNB : (derivedNeighborhood S G).space ⊆ B.space := by
    intro x hx
    apply hBspace.symm.subset
    exact ⟨hST.space_eq.subset (derivedNeighborhood_space_subset S G hx),
      (interior_subset : interior D ⊆ D) (hsmall (mem_image_of_mem T.map hx)).2⟩
  have hNspace : (derivedNeighborhood S G).space = (derivedNeighborhood B G).space := by
    have he := derivedNeighborhood_space_inter_subcomplex S B G (restrict_faces_subset S P)
    rwa [inter_eq_left.mpr hNB] at he
  have hsolid : IsTopologicalSolidTorus (derivedNeighborhood S G).space := by
    rw [hNspace]
    exact (isCombinatorialSolidTorus_derivedNeighborhood_circle B G
      hBball.isCombinatorialManifoldWithBoundary hGB hG.isCombinatorialManifold
      hG.isConnected (isOrientable_of_isPLBall hBball)).1
  have hNT : (derivedNeighborhood S G).space ⊆ T.complex.space :=
    (derivedNeighborhood_space_subset S G).trans hST.space_eq.subset
  let f : (derivedNeighborhood S G).space → X := fun x => T.map x
  have hf : IsEmbedding f := T.isEmbedding.comp (IsEmbedding.inclusion hNT)
  have hrange : range f = T.map '' (derivedNeighborhood S G).space := by
    exact (Set.image_eq_range T.map (derivedNeighborhood S G).space).symm
  obtain ⟨φ⟩ := hsolid
  refine ⟨T.map '' (derivedNeighborhood S G).space, himage ▸ hreg, ?_, hsmall⟩
  exact ⟨((hf.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm).trans φ⟩

theorem IsPLDerivedNeighborhoodExhaustion.exists_nested_solidTorus_regularNeighborhoods
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O D : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C)
    (hD : IsPolyhedralBall (n := 3) 3 D) (hDU : D ⊆ U) (hCD : C ⊆ interior D)
    (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ S T : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsLocallyFiniteRegularNeighborhoodOf (n := 3) T C U ∧
      IsTopologicalSolidTorus S ∧ IsTopologicalSolidTorus T ∧
      T ⊆ interior S ∧ S ⊆ O ∩ interior D := by
  obtain ⟨S, hS, htS, hSO⟩ :=
    h.exists_solidTorus_regularNeighborhood_subset_open hU hC hD hDU hCD hO hCO
  have hCS : C ⊆ interior S := subset_interior_iff_mem_nhdsSet.mpr hS.mem_nhdsSet
  obtain ⟨T, hT, htT, hTS⟩ := h.exists_solidTorus_regularNeighborhood_subset_open
    hU hC hD hDU hCD isOpen_interior hCS
  exact ⟨S, T, hS, hT, htS, htT, hTS.trans inter_subset_left, hSO⟩

end DifferentialGeometry.Topology.PiecewiseLinear
