/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcComplement
import DifferentialGeometry.Topology.PiecewiseLinear.CurveInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplementLink
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.complement_two
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K)
    (hA : IsCombinatorialManifoldWithBoundary 2 A) (hAK : A.faces ⊆ K.faces) :
    IsCombinatorialManifoldWithBoundary 2 (subcomplexGeneratedBy K A.facesᶜ) := by
  intro v hv
  have hvK := subcomplexGeneratedBy_faces_subset K A.facesᶜ hv
  by_cases hvA : {v} ∈ A.faces
  · let L := SimplicialComplex.geometricLink K {v}
    let B := SimplicialComplex.geometricLink A {v}
    have hBL : B.faces ⊆ L.faces := fun _ ht => ⟨ht.1, ht.2.1, hAK ht.2.2⟩
    have hsub : B.space ⊆ L.space := space_mono_of_faces_subset hBL
    have hnot : ¬L.space ⊆ B.space :=
      not_geometricLink_space_subset_of_mem_subcomplexGeneratedBy_compl K A hAK hvA hv
    rw [geometricLink_subcomplexGeneratedBy_compl_space K A hAK v]
    rcases hA v hvA with hBsphere | hB
    · exact (hnot (eq_of_subset_of_isPLSphere_one hBsphere (hK v hvK) hsub).symm.subset).elim
    · exact Or.inr ((hK v hvK).isPLBall_closure_sdiff_one hB hsub)
  · rw [geometricLink_subcomplexGeneratedBy_compl_of_notMem K A hvA]
    exact Or.inl (hK v hvK)

open Classical in
theorem IsCombinatorialManifold.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_two
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifold 2 K)
    (hA : IsCombinatorialManifoldWithBoundary 2 A) (hAK : A.space ⊆ K.space) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 R ∧ R.space = closure (K.space \ A.space) ∧
      (boundaryComplex 2 R).space = (boundaryComplex 2 A).space := by
  obtain ⟨T, hT, hTfin, hTA⟩ := exists_isSubdivision_restrict_isSubdivision K A hAK
  let _ : Finite T.faces := hTfin.to_subtype
  let B := restrict T A.space
  let _ : Finite B.faces := (restrict_faces_finite T A.space).to_subtype
  let R := subcomplexGeneratedBy T B.facesᶜ
  let _ : Finite R.faces := (subcomplexGeneratedBy_faces_finite T B.facesᶜ).to_subtype
  let _ : Finite (boundaryComplex 2 A).faces := (boundaryComplex_faces_finite 2 A).to_subtype
  have hR : IsCombinatorialManifoldWithBoundary 2 R :=
    (hK.of_isSubdivision hT).complement_two T B (hA.of_isSubdivision hTA)
      (restrict_faces_subset T A.space)
  have hRspace : R.space = closure (K.space \ A.space) := by
    rw [show R = subcomplexGeneratedBy T B.facesᶜ from rfl,
      ← closure_space_sdiff_space_eq_subcomplexGeneratedBy T T B Subset.rfl
        (restrict_faces_subset T A.space), hT.space_eq, hTA.space_eq]
  have hbd : (boundaryComplex 2 K).space = ∅ := by
    rw [Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty K]
    simp
  refine ⟨R, Set.toFinite _, hR, hRspace, ?_⟩
  rw [boundaryComplex_space_of_closure_sdiff K A R hK.isCombinatorialManifoldWithBoundary
    hA hAK hR hRspace, hbd, empty_sdiff, closure_empty, empty_union, sdiff_empty]
  exact (isPolyhedron_space (boundaryComplex 2 A)).isClosed.closure_eq

end DifferentialGeometry.Topology.PiecewiseLinear
