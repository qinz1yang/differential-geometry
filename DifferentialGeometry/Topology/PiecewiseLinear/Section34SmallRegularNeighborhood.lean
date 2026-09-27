/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34NestedPiercingSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodSurgery

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLDerivedNeighborhoodExhaustion.exists_regularNeighborhood_subset_open
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C) (hCU : C ⊆ U)
    (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ S : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧ S ⊆ O := by
  classical
  obtain ⟨m, T, A, -, hcover, hfin, -, -, hman, -, hmono, -⟩ := h
  let _ : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  let Q := T.complex.space ∩ T.map ⁻¹' C
  have hQ : IsPLSphere 1 Q :=
    T.isPLSphere_preimage_of_isPolyhedralSphere A hcover hfin hmono hC hCU
  obtain ⟨R, hR, hnew, hRQ⟩ := T.exists_isSubdivision_restrict_space_finite_change
    A hcover hfin hmono hQ.isPolyhedron inter_subset_left
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
  let W : Bool → Set X := fun b => if b then O else Cᶜ
  have hW : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact hCc.isClosed.isOpen_compl
    · exact hO
  have hUW : U ⊆ ⋃ b, W b := by
    intro x _
    by_cases hxC : x ∈ C
    · exact mem_iUnion.mpr ⟨true, hCO hxC⟩
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
  refine ⟨T.map '' (derivedNeighborhood S G).space, himage ▸ hreg, ?_⟩
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨s, hs, ⟨y, hys, hyG⟩, hzs⟩ := exists_face_meets_of_mem_derivedNeighborhood_space hz
  obtain ⟨b, hb⟩ := hstar s hs
  obtain ⟨v, hv⟩ := S.nonempty_of_mem_faces hs
  have hyW := hb v hv s hs hv (mem_image_of_mem T.map hys)
  have hzW := hb v hv s hs hv (mem_image_of_mem T.map hzs)
  cases b
  · exact (hyW ((hGspace.subset hyG).2)).elim
  · exact hzW

theorem IsPLDerivedNeighborhoodExhaustion.exists_nested_regularNeighborhoods_subset_open
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C O : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C) (hCU : C ⊆ U)
    (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ S T : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U ∧
      IsLocallyFiniteRegularNeighborhoodOf (n := 3) T C U ∧ T ⊆ interior S ∧ S ⊆ O := by
  obtain ⟨S, hS, hSO⟩ := h.exists_regularNeighborhood_subset_open hU hC hCU hO hCO
  have hCS : C ⊆ interior S := subset_interior_iff_mem_nhdsSet.mpr hS.mem_nhdsSet
  obtain ⟨T, hT, hTS⟩ :=
    h.exists_regularNeighborhood_subset_open hU hC hCU isOpen_interior hCS
  exact ⟨S, T, hS, hT, hTS, hSO⟩

end DifferentialGeometry.Topology.PiecewiseLinear
