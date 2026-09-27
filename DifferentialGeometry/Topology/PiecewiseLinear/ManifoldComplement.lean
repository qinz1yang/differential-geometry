/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplementLink
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.complement
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.faces ⊆ K.faces)
    (hD : IsCombinatorialManifoldWithBoundary 2 (restrict A (boundaryComplex 3 K).space)) :
    IsCombinatorialManifoldWithBoundary 3 (subcomplexGeneratedBy K A.facesᶜ) := by
  classical
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
    change IsPLSphere 2 (closure (L.space \ B.space)) ∨ IsPLBall 2 (closure (L.space \ B.space))
    rcases hA v hvA with hBsphere | hB
    · rcases hK v hvK with hLsphere | hLball
      · exact (hnot (eq_of_subset_of_isPLSphere hBsphere hLsphere hsub).symm.subset).elim
      · exact (hBsphere.not_subset_of_isPLBall hLball hsub).elim
    · right
      rcases hK v hvK with hLsphere | hLball
      · exact hLsphere.isPLBall_closure_sdiff hB hsub
      · have hvbd : {v} ∈ (boundaryComplex 3 K).faces := by
          apply (hK.mem_boundaryComplex_faces_iff K).mpr
          exact ⟨hvK, by simp, by simpa only [Finset.card_singleton] using hLball⟩
        have hvD : {v} ∈ (restrict A (boundaryComplex 3 K).space).faces :=
          (mem_restrict_faces_iff_of_faces_subset K A (boundaryComplex 3 K) hAK
            (boundaryComplex_faces_subset 3 K)).mpr ⟨hvA, hvbd⟩
        have hmeet : (SimplicialComplex.geometricLink
            (restrict A (boundaryComplex 3 K).space) {v}).space =
              B.space ∩ (boundaryComplex 2 L).space := by
          rw [geometricLink_restrict_space_of_faces_subset K A (boundaryComplex 3 K) hAK
            (boundaryComplex_faces_subset 3 K), geometricLink_boundaryComplex]
          exact restrict_space_eq_inter_of_faces_subset L B (boundaryComplex 2 L) hBL
            (boundaryComplex_faces_subset 2 L)
        have htrace := hD v hvD
        rw [hmeet] at htrace
        rcases htrace with hs | hb
        · have heq := eq_of_subset_of_isPLSphere hs
            (isPLSphere_boundaryComplex_space_of_isPLBall L hLball) inter_subset_right
          have hbd : (boundaryComplex 2 L).space ⊆ B.space :=
            heq.symm.subset.trans inter_subset_left
          exact (hnot (eq_of_isPLBall_of_boundaryComplex_subset L hLball hB hsub
              hbd).symm.subset).elim
        · exact isPLBall_closure_sdiff_of_inter_boundaryComplex L hLball hB hsub hb
  · rw [geometricLink_subcomplexGeneratedBy_compl_of_notMem K A hvA]
    exact hK v hvK

open Classical in
theorem IsCombinatorialManifoldWithBoundary.complement_of_inter_boundary_isPLBall
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.faces ⊆ K.faces)
    (hD : IsPLBall 2 (A.space ∩ (boundaryComplex 3 K).space)) :
    IsCombinatorialManifoldWithBoundary 3 (subcomplexGeneratedBy K A.facesᶜ) := by
  let _ : Finite (restrict A (boundaryComplex 3 K).space).faces :=
    (restrict_faces_finite _ _).to_subtype
  apply hK.complement K A hA hAK
  have hspace := restrict_space_eq_inter_of_faces_subset K A (boundaryComplex 3 K) hAK
    (boundaryComplex_faces_subset 3 K)
  exact (hspace.symm ▸ hD).isCombinatorialManifoldWithBoundary

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isCombinatorialManifoldWithBoundary_closure_sdiff
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {C : Set E}
    (hC : IsPLBall 3 C) (hCK : C ⊆ K.space)
    (hD : IsPLBall 2 (C ∩ (boundaryComplex 3 K).space)) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 R ∧ R.space = closure (K.space \ C) := by
  classical
  obtain ⟨J, hJ, hJfin, hJC⟩ := exists_isSubdivision_restrict_space K hC.isPolyhedron hCK
  let _ : Finite J.faces := hJfin.to_subtype
  let A := restrict J C
  let _ : Finite A.faces := (restrict_faces_finite J C).to_subtype
  have hA : IsPLBall 3 A.space := hJC.symm ▸ hC
  have hD' : IsPLBall 2 (A.space ∩ (boundaryComplex 3 J).space) := by
    rw [show A.space = C from hJC, boundaryComplex_space_of_isSubdivision K J hK hJ]
    exact hD
  have hcomp := (hK.of_isSubdivision hJ).complement_of_inter_boundary_isPLBall J A
    hA.isCombinatorialManifoldWithBoundary (restrict_faces_subset J C) hD'
  refine ⟨subcomplexGeneratedBy J A.facesᶜ, subcomplexGeneratedBy_faces_finite J A.facesᶜ,
    hcomp, ?_⟩
  rw [← closure_space_sdiff_space_eq_subcomplexGeneratedBy J J A Subset.rfl
    (restrict_faces_subset J C), hJ.space_eq, show A.space = C from hJC]

end DifferentialGeometry.Topology.PiecewiseLinear
