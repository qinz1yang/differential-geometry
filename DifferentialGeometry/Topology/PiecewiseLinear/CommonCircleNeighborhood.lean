/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CommonCircleDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleNeighborhood

/-!
# Common polyhedral neighborhoods of a circle on two surfaces
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
def IsCommonAnnularDerivedNeighborhood
    (K : Geometry.SimplicialComplex ℝ E) (N J S₀ S₁ : Set E) : Prop :=
  ∃ R L P₀ P₁ : Geometry.SimplicialComplex ℝ E,
    R.faces.Finite ∧ L.faces.Finite ∧ P₀.faces.Finite ∧ P₁.faces.Finite ∧
    IsSubdivision R K ∧ L.space = J ∧ P₀.space = S₀ ∧ P₁.space = S₁ ∧
    P₀.faces ⊆ R.faces ∧ P₁.faces ⊆ R.faces ∧
    L.faces ⊆ P₀.faces ∧ L.faces ⊆ P₁.faces ∧
    (derivedNeighborhood R L).space = N ∧ N ∈ nhdsSetWithin J K.space ∧
    N ∩ S₀ = (derivedNeighborhood P₀ L).space ∧
    N ∩ S₁ = (derivedNeighborhood P₁ L).space ∧
    (∃ H : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn H (stdSimplexBoundary 2 ×ˢ Icc 0 1) (N ∩ S₀)) ∧
    ∃ H : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn H (stdSimplexBoundary 2 ×ˢ Icc 0 1) (N ∩ S₁)

open Classical in
theorem IsCommonAnnularDerivedNeighborhood.isPolyhedron
    {K : Geometry.SimplicialComplex ℝ E} {N J S₀ S₁ : Set E}
    (h : IsCommonAnnularDerivedNeighborhood K N J S₀ S₁) : IsPolyhedron N := by
  obtain ⟨R, L, -, -, hRfin, -, -, -, -, -, -, -, -, -, -, -, hN, -⟩ := h
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite (derivedNeighborhood R L).faces :=
    (derivedNeighborhood_faces_finite R L).to_subtype
  rw [← hN]
  exact isPolyhedron_space (derivedNeighborhood R L)

omit [FiniteDimensional ℝ E] in
open Classical in
theorem IsCommonAnnularDerivedNeighborhood.subset_ambient
    {K : Geometry.SimplicialComplex ℝ E} {N J S₀ S₁ : Set E}
    (h : IsCommonAnnularDerivedNeighborhood K N J S₀ S₁) : N ⊆ K.space := by
  obtain ⟨R, L, -, -, -, -, -, -, hRK, -, -, -, -, -, -, -, hN, -⟩ := h
  rw [← hN]
  exact (derivedNeighborhood_space_subset R L).trans hRK.space_eq.subset

omit [FiniteDimensional ℝ E] in
open Classical in
theorem IsCommonAnnularDerivedNeighborhood.mem_nhdsSetWithin
    {K : Geometry.SimplicialComplex ℝ E} {N J S₀ S₁ : Set E}
    (h : IsCommonAnnularDerivedNeighborhood K N J S₀ S₁) :
    N ∈ nhdsSetWithin J K.space := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hN, -⟩ := h
  exact hN

def IsNestedCommonAnnularDerivedNeighborhood
    (K : Geometry.SimplicialComplex ℝ E) (A B J S₀ S₁ : Set E) : Prop :=
  IsCommonAnnularDerivedNeighborhood K A J S₀ S₁ ∧
  IsCommonAnnularDerivedNeighborhood K B J S₀ S₁ ∧
  ∃ O : Set E, IsOpen O ∧ J ⊆ O ∧ B ⊆ O ∩ K.space ∧ O ∩ K.space ⊆ A

omit [FiniteDimensional ℝ E] in
theorem IsNestedCommonAnnularDerivedNeighborhood.inner_subset_outer
    {K : Geometry.SimplicialComplex ℝ E} {A B J S₀ S₁ : Set E}
    (h : IsNestedCommonAnnularDerivedNeighborhood K A B J S₀ S₁) : B ⊆ A := by
  obtain ⟨-, -, O, -, -, hBO, hOA⟩ := h
  exact hBO.trans hOA

open Classical in
theorem exists_common_annular_derivedNeighborhood
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {J S₀ S₁ U : Set E}
    (hJ : IsPLSphere 1 J) (hS₀ : IsPLSphere 2 S₀) (hS₁ : IsPLSphere 2 S₁)
    (hJK : J ⊆ K.space) (hS₀K : S₀ ⊆ K.space) (hS₁K : S₁ ⊆ K.space)
    (hJS₀ : J ⊆ S₀) (hJS₁ : J ⊆ S₁) (hU : IsOpen U) (hJU : J ⊆ U) :
    ∃ N : Set E, IsCommonAnnularDerivedNeighborhood K N J S₀ S₁ ∧ N ⊆ U := by
  obtain ⟨R, L, P₀, P₁, hRfin, hLfin, hP₀fin, hP₁fin, hRK, hLspace,
    hP₀space, hP₁space, hP₀R, hP₁R, hLP₀, hLP₁, hNsubU, hNnhds, htrace₀,
    htrace₁⟩ :=
    exists_common_derivedNeighborhood_with_surface_traces K hJ.isPolyhedron
      hS₀.isPolyhedron hS₁.isPolyhedron hJK hS₀K hS₁K hJS₀ hJS₁ hU hJU
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let _ : Finite P₀.faces := hP₀fin.to_subtype
  let _ : Finite P₁.faces := hP₁fin.to_subtype
  have hL' : IsPLSphere 1 L.space := hLspace.symm ▸ hJ
  have hP₀' : IsPLSphere 2 P₀.space := hP₀space.symm ▸ hS₀
  have hP₁' : IsPLSphere 2 P₁.space := hP₁space.symm ▸ hS₁
  obtain ⟨H₀, hH₀⟩ := exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle P₀ L
    hP₀'.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hLP₀
    hL'.isCombinatorialManifold hL'.isConnected (isOrientable_of_isPLSphere hP₀')
  obtain ⟨H₁, hH₁⟩ := exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle P₁ L
    hP₁'.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hLP₁
    hL'.isCombinatorialManifold hL'.isConnected (isOrientable_of_isPLSphere hP₁')
  exact ⟨(derivedNeighborhood R L).space,
    ⟨R, L, P₀, P₁, hRfin, hLfin, hP₀fin, hP₁fin, hRK, hLspace, hP₀space,
      hP₁space, hP₀R, hP₁R, hLP₀, hLP₁, rfl, hNnhds, htrace₀, htrace₁,
      ⟨H₀, htrace₀ ▸ hH₀⟩, H₁, htrace₁ ▸ hH₁⟩,
    hNsubU⟩

open Classical in
theorem exists_nested_common_annular_derivedNeighborhoods
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {J S₀ S₁ U : Set E}
    (hJ : IsPLSphere 1 J) (hS₀ : IsPLSphere 2 S₀) (hS₁ : IsPLSphere 2 S₁)
    (hJK : J ⊆ K.space) (hS₀K : S₀ ⊆ K.space) (hS₁K : S₁ ⊆ K.space)
    (hJS₀ : J ⊆ S₀) (hJS₁ : J ⊆ S₁) (hU : IsOpen U) (hJU : J ⊆ U) :
    ∃ A B : Set E,
      A ⊆ U ∧ IsNestedCommonAnnularDerivedNeighborhood K A B J S₀ S₁ := by
  obtain ⟨A, hA, hAU⟩ := exists_common_annular_derivedNeighborhood K hJ hS₀ hS₁
    hJK hS₀K hS₁K hJS₀ hJS₁ hU hJU
  obtain ⟨O, hOopen, hJO, hOKA⟩ := mem_nhdsSetWithin.mp hA.mem_nhdsSetWithin
  obtain ⟨B, hB, hBO⟩ := exists_common_annular_derivedNeighborhood K hJ hS₀ hS₁
    hJK hS₀K hS₁K hJS₀ hJS₁ hOopen hJO
  exact ⟨A, B, hAU, hA, hB, O, hOopen, hJO,
    fun x hx => ⟨hBO hx, hB.subset_ambient hx⟩, hOKA⟩

end DifferentialGeometry.Topology.PiecewiseLinear
