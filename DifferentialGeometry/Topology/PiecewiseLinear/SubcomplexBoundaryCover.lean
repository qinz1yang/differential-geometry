/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem boundaryComplex_space_subset_boundary_union_closure_sdiff {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.faces ⊆ K.faces) :
    (boundaryComplex (n + 1) A).space ⊆
      (boundaryComplex (n + 1) K).space ∪ closure (K.space \ A.space) := by
  let B := boundaryComplex (n + 1) A
  let _ : Finite B.faces := (boundaryComplex_faces_finite (n + 1) A).to_subtype
  have hB := isCombinatorialManifold_boundaryComplex A hA
  intro x hx
  obtain ⟨s, hs, hxs⟩ := B.mem_space_iff.mp hx
  obtain ⟨t, ht, hst, htc⟩ := hB.exists_face_superset_card_eq B hs
  have hxt := convexHull_mono (Finset.coe_subset.mpr hst) hxs
  by_cases htB : t ∈ (boundaryComplex (n + 1) K).faces
  · exact Or.inl ((boundaryComplex (n + 1) K).convexHull_subset_space htB hxt)
  · right
    have htA := boundaryComplex_faces_subset (n + 1) A ht
    obtain ⟨a, ha⟩ := (hA.mem_boundaryComplex_iff_unique_coface A htc).mp ht
    obtain ⟨b, c, hbc, hbcV⟩ := hK.codimension_one_cofaces_of_notMem_boundary K
      (hAK htA) htc htB
    have hbK : b ∉ t ∧ insert b t ∈ K.faces := hbcV.symm.subset (Or.inl rfl)
    have hcK : c ∉ t ∧ insert c t ∈ K.faces := hbcV.symm.subset (Or.inr rfl)
    have hex : ∃ w, w ∉ t ∧ insert w t ∈ K.faces ∧ insert w t ∉ A.faces := by
      by_cases hba : b = a
      · refine ⟨c, hcK.1, hcK.2, ?_⟩
        intro hcA
        have hca : c = a := ha.subset ⟨hcK.1, hcA⟩
        exact hbc (hba.trans hca.symm)
      · exact ⟨b, hbK.1, hbK.2, fun hbA => hba (ha.subset ⟨hbK.1, hbA⟩)⟩
    obtain ⟨w, -, hwK, hwA⟩ := hex
    rw [closure_space_sdiff_space_eq_subcomplexGeneratedBy K K A subset_rfl hAK]
    exact (subcomplexGeneratedBy K A.facesᶜ).convexHull_subset_space
      ⟨insert w t, ⟨hwK, hwA⟩, Finset.subset_insert w t, A.nonempty_of_mem_faces htA⟩ hxt

open Classical in
theorem boundaryComplex_space_eq_inter_boundary_union_closure_sdiff {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.faces ⊆ K.faces) :
    (boundaryComplex (n + 1) A).space = A.space ∩
      ((boundaryComplex (n + 1) K).space ∪ closure (K.space \ A.space)) := by
  apply Subset.antisymm
  · exact subset_inter (boundaryComplex_space_subset (n + 1) A)
      (boundaryComplex_space_subset_boundary_union_closure_sdiff K A hK hA hAK)
  · rintro x ⟨hxA, hxB | hxR⟩
    · exact inter_boundaryComplex_space_subset K A hK hA hAK ⟨hxA, hxB⟩
    · exact inter_closure_sdiff_space_subset_boundaryComplex K A hK hA hAK ⟨hxA, hxR⟩

end DifferentialGeometry.Topology.PiecewiseLinear
