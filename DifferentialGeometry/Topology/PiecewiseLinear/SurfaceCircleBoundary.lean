/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleCollar
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_surface_of_circle_collars
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {P B : Set E}
    (hP : IsPolyhedron P) (hPK : P ⊆ K.space)
    (hnear : ∀ x ∈ P \ B, P ∈ 𝓝[K.space] x)
    (hcollar : ∀ x ∈ B, ∃ G : Set E, x ∈ G ∧ HasPLCircleCollar P G) :
    ∃ (Q : Geometry.SimplicialComplex ℝ E) (hQfin : Q.faces.Finite),
      letI := hQfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 Q ∧ Q.space = P ∧
      (boundaryComplex 2 Q).space = B := by
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  obtain ⟨Q, hQfin, hQspace⟩ := hP.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hmodel : ∀ x ∈ B, ∃ (A : Geometry.SimplicialComplex ℝ E) (hAfin : A.faces.Finite),
      letI := hAfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 A ∧ A.space ⊆ P ∧
        A.space ∈ 𝓝[P] x ∧ x ∈ (boundaryComplex 2 A).space := by
    intro x hx
    obtain ⟨G, hxG, hG⟩ := hcollar x hx
    obtain ⟨W, ρ, hρ, hρ0, hW, hWnear⟩ := hG.2 univ isOpen_univ (subset_univ _)
    obtain ⟨A, hAfin, hA, -, hAspace, hAb⟩ := hρ.exists_annulus_complex hG.1 zero_lt_one
    let _ : Finite A.faces := hAfin.to_subtype
    refine ⟨A, hAfin, hA, hAspace.subset.trans (hW.trans inter_subset_left), ?_, ?_⟩
    · obtain ⟨O, hO, hGO, hOW⟩ := mem_nhdsSetWithin.mp hWnear
      rw [hAspace]
      exact mem_nhdsWithin.mpr ⟨O, hO, hGO hxG, hOW⟩
    · rw [hAb]
      exact ⟨(x, 0), ⟨hxG, Or.inl rfl⟩, hρ0 x hxG⟩
  have hQ : IsCombinatorialManifoldWithBoundary 2 Q := by
    intro x hx
    have hxP : x ∈ P := hQspace ▸ Q.subset_space hx (Finset.mem_singleton_self x)
    by_cases hxB : x ∈ B
    · obtain ⟨A, hAfin, hA, hAP, hAnear, -⟩ := hmodel x hxB
      let _ : Finite A.faces := hAfin.to_subtype
      exact isPLSphere_or_isPLBall_geometricLink_of_manifold_neighborhood Q A hA
        (hAP.trans hQspace.symm.subset) hx (hQspace.symm ▸ hAnear)
    · obtain ⟨D, hD, hDKP, hDnear⟩ :=
        hK.isCombinatorialManifoldWithBoundary.exists_isPLBall_subset_of_mem_nhdsWithin
          (hPK hxP) (hnear x ⟨hxP, hxB⟩)
      obtain ⟨A, hAfin, hAspace⟩ := hD.isPolyhedron.exists_simplicialComplex
      let _ : Finite A.faces := hAfin.to_subtype
      have hA : IsPLBall 2 A.space := hAspace.symm ▸ hD
      have hAP := hAspace.subset.trans (hDKP.trans inter_subset_right)
      have hAnear : A.space ∈ 𝓝[P] x :=
        hAspace.symm ▸ (nhdsWithin_mono x hPK) hDnear
      exact isPLSphere_or_isPLBall_geometricLink_of_manifold_neighborhood Q A
        hA.isCombinatorialManifoldWithBoundary (hAP.trans hQspace.symm.subset) hx
        (hQspace.symm ▸ hAnear)
  have hKb : (boundaryComplex 2 K).space = ∅ := by
    rw [Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty K]
    simp
  refine ⟨Q, hQfin, hQ, hQspace, ?_⟩
  ext x
  constructor
  · intro hxB
    by_contra hxnot
    have hxQ := boundaryComplex_space_subset 2 Q hxB
    have hxP : x ∈ P := hQspace ▸ hxQ
    have hxK := (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin (n := 1) K Q
      hK.isCombinatorialManifoldWithBoundary hQ (hQspace.subset.trans hPK) hxQ
      (hQspace.symm ▸ hnear x ⟨hxP, hxnot⟩)).mp hxB
    rw [hKb] at hxK
    exact hxK
  · intro hxB
    obtain ⟨A, hAfin, hA, hAP, hAnear, hxA⟩ := hmodel x hxB
    let _ : Finite A.faces := hAfin.to_subtype
    exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin (n := 1) Q A hQ hA
      (hAP.trans hQspace.symm.subset) (boundaryComplex_space_subset 2 A hxA)
      (hQspace.symm ▸ hAnear)).mp hxA

end DifferentialGeometry.Topology.PiecewiseLinear
