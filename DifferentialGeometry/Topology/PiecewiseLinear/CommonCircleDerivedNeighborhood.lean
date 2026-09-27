/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexMesh

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_common_derivedNeighborhood_with_surface_traces
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {J S₀ S₁ U : Set E}
    (hJ : IsPolyhedron J) (hS₀ : IsPolyhedron S₀) (hS₁ : IsPolyhedron S₁)
    (hJK : J ⊆ K.space) (hS₀K : S₀ ⊆ K.space) (hS₁K : S₁ ⊆ K.space)
    (hJS₀ : J ⊆ S₀) (hJS₁ : J ⊆ S₁) (hU : IsOpen U) (hJU : J ⊆ U) :
    ∃ R L P₀ P₁ : Geometry.SimplicialComplex ℝ E,
      R.faces.Finite ∧ L.faces.Finite ∧ P₀.faces.Finite ∧ P₁.faces.Finite ∧
      IsSubdivision R K ∧ L.space = J ∧ P₀.space = S₀ ∧ P₁.space = S₁ ∧
      P₀.faces ⊆ R.faces ∧ P₁.faces ⊆ R.faces ∧
      L.faces ⊆ P₀.faces ∧ L.faces ⊆ P₁.faces ∧
      (derivedNeighborhood R L).space ⊆ U ∧
      (derivedNeighborhood R L).space ∈ nhdsSetWithin J K.space ∧
      (derivedNeighborhood R L).space ∩ S₀ = (derivedNeighborhood P₀ L).space ∧
      (derivedNeighborhood R L).space ∩ S₁ = (derivedNeighborhood P₁ L).space := by
  classical
  obtain ⟨K₀, hK₀, hK₀fin, hS₀space⟩ :=
    exists_isSubdivision_restrict_space K hS₀ hS₀K
  let _ : Finite K₀.faces := hK₀fin.to_subtype
  have hS₁K₀ : S₁ ⊆ K₀.space := hS₁K.trans hK₀.space_eq.symm.subset
  obtain ⟨K₁, hK₁, hK₁fin, hS₁space⟩ :=
    exists_isSubdivision_restrict_space K₀ hS₁ hS₁K₀
  let _ : Finite K₁.faces := hK₁fin.to_subtype
  have hJK₁ : J ⊆ K₁.space :=
    hJK.trans (hK₀.space_eq.symm.subset.trans hK₁.space_eq.symm.subset)
  obtain ⟨R₀, hR₀, hR₀fin, hJspace⟩ :=
    exists_isSubdivision_restrict_space K₁ hJ hJK₁
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  let L₀ := restrict R₀ J
  let T₀ := restrict K₀ S₀
  let T₁ := restrict K₁ S₁
  let Q₀ := restrict R₀ T₀.space
  let Q₁ := restrict R₀ T₁.space
  have hQ₀sub : IsSubdivision Q₀ T₀ :=
    (hR₀.trans hK₁).restrict T₀ (restrict_faces_subset K₀ S₀)
  have hQ₁sub : IsSubdivision Q₁ T₁ :=
    hR₀.restrict T₁ (restrict_faces_subset K₁ S₁)
  have hQ₀space : Q₀.space = S₀ := hQ₀sub.space_eq.trans hS₀space
  have hQ₁space : Q₁.space = S₁ := hQ₁sub.space_eq.trans hS₁space
  obtain ⟨δ, hδ, hthick⟩ :=
    hJ.isCompact.exists_cthickening_subset_open hU hJU
  obtain ⟨R, hR, hRfin, hdiam, hLsub⟩ :=
    exists_isSubdivision_diam_lt_restrict_isSubdivision R₀ L₀
      (restrict_faces_subset R₀ J) hδ
  let _ : Finite R.faces := hRfin.to_subtype
  let L := restrict R L₀.space
  let P₀ := restrict R Q₀.space
  let P₁ := restrict R Q₁.space
  have hLfin := restrict_faces_finite R L₀.space
  have hP₀fin := restrict_faces_finite R Q₀.space
  have hP₁fin := restrict_faces_finite R Q₁.space
  have hP₀sub : IsSubdivision P₀ Q₀ :=
    hR.restrict Q₀ (restrict_faces_subset R₀ T₀.space)
  have hP₁sub : IsSubdivision P₁ Q₁ :=
    hR.restrict Q₁ (restrict_faces_subset R₀ T₁.space)
  have hLspace : L.space = J := hLsub.space_eq.trans hJspace
  have hP₀space : P₀.space = S₀ := hP₀sub.space_eq.trans hQ₀space
  have hP₁space : P₁.space = S₁ := hP₁sub.space_eq.trans hQ₁space
  have hLP₀ : L.faces ⊆ P₀.faces := by
    rintro s ⟨hsR, hsL⟩
    exact ⟨hsR, hsL.trans (hJspace.subset.trans (hJS₀.trans hQ₀space.symm.subset))⟩
  have hLP₁ : L.faces ⊆ P₁.faces := by
    rintro s ⟨hsR, hsL⟩
    exact ⟨hsR, hsL.trans (hJspace.subset.trans (hJS₁.trans hQ₁space.symm.subset))⟩
  have hRK : IsSubdivision R K := hR.trans (hR₀.trans (hK₁.trans hK₀))
  have hNsubU : (derivedNeighborhood R L).space ⊆ U := by
    apply derivedNeighborhood_space_subset_of_forall_face
    intro s hs t ht hst z hzt
    apply hthick
    apply Metric.mem_cthickening_of_dist_le z (s.centroid ℝ id) δ J
      (hLspace.subset (L.convexHull_subset_space hs
        (s.centroid_mem_convexHull (L.nonempty_of_mem_faces hs))))
    exact ((Metric.dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded
      hzt hst).trans_lt (hdiam t ht)).le
  have hNnhdsPoint : ∀ x ∈ J, (derivedNeighborhood R L).space ∈ 𝓝[K.space] x := by
    intro x hx
    rw [← hRK.space_eq]
    exact derivedNeighborhood_mem_nhdsWithin (restrict_faces_subset R L₀.space)
      (hLspace.symm.subset hx)
  have hNnhds : (derivedNeighborhood R L).space ∈ nhdsSetWithin J K.space := by
    choose O hOopen hxO hOsub using fun x : J => mem_nhdsWithin.mp (hNnhdsPoint x x.2)
    refine mem_nhdsSetWithin.mpr ⟨⋃ x : J, O x, isOpen_iUnion hOopen, ?_, ?_⟩
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩
    · rintro x ⟨hxO, hxK⟩
      obtain ⟨y, hxy⟩ := mem_iUnion.mp hxO
      exact hOsub y ⟨hxy, hxK⟩
  have htrace₀ :
      (derivedNeighborhood R L).space ∩ S₀ = (derivedNeighborhood P₀ L).space := by
    rw [← hP₀space]
    exact derivedNeighborhood_space_inter_subcomplex R P₀ L
      (restrict_faces_subset R Q₀.space)
  have htrace₁ :
      (derivedNeighborhood R L).space ∩ S₁ = (derivedNeighborhood P₁ L).space := by
    rw [← hP₁space]
    exact derivedNeighborhood_space_inter_subcomplex R P₁ L
      (restrict_faces_subset R Q₁.space)
  exact ⟨R, L, P₀, P₁, hRfin, hLfin, hP₀fin, hP₁fin, hRK, hLspace,
    hP₀space, hP₁space, restrict_faces_subset R Q₀.space,
    restrict_faces_subset R Q₁.space, hLP₀, hLP₁, hNsubU, hNnhds, htrace₀, htrace₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
