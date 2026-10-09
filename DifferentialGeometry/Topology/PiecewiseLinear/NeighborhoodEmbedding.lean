/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsPLHomeomorphOn.image_mem_nhdsWithin_of_notMem_boundaryComplex
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    {P : Set E} {Q : Set F} {f : E → F} (hf : IsPLHomeomorphOn f P Q)
    (hQL : Q ⊆ L.space) {x : E} (hx : x ∈ K.space)
    (hxB : x ∉ (boundaryComplex (n + 1) K).space) (hP : P ∈ 𝓝[K.space] x) :
    Q ∈ 𝓝[L.space] f x := by
  classical
  obtain ⟨D, hD, hDKP, hDnhds⟩ := hK.exists_isPLBall_subset_of_mem_nhdsWithin hx hP
  obtain ⟨A, hAfin, hAspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hA : IsPLBall (n + 1) A.space := hAspace.symm ▸ hD
  have hAK : A.space ⊆ K.space := hAspace.subset.trans (hDKP.trans inter_subset_left)
  have hAP : A.space ⊆ P := hAspace.subset.trans (hDKP.trans inter_subset_right)
  have hxA : x ∈ A.space := hAspace.symm.subset (mem_of_mem_nhdsWithin hx hDnhds)
  have hxAB : x ∉ (boundaryComplex (n + 1) A).space := fun h => hxB
    ((mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K A hK
      hA.isCombinatorialManifoldWithBoundary hAK hxA (hAspace.symm ▸ hDnhds)).mp h)
  have hfA := hf.restrict hA.isPolyhedron hAP
  obtain ⟨B, hBfin, hBspace⟩ := (hA.of_isPLHomeomorphOn hfA).isPolyhedron.exists_simplicialComplex
  let _ : Finite B.faces := hBfin.to_subtype
  have hfAB : IsPLHomeomorphOn f A.space B.space := hBspace.symm ▸ hfA
  have hB := hA.isCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn hfAB
  have hBQ : B.space ⊆ Q := hBspace.subset.trans ((image_mono hAP).trans hf.image_eq.subset)
  have hBL := hBQ.trans hQL
  have hfxB : f x ∈ B.space := hfAB.bijOn.mapsTo hxA
  have hfxBd : f x ∉ (boundaryComplex (n + 1) B).space := fun h =>
    hxAB ((mem_boundaryComplex_space_iff_of_isPLHomeomorphOn A B
      hA.isCombinatorialManifoldWithBoundary hfAB hxA).mp h)
  have hnot : f x ∉ closure (L.space \ B.space) := fun h => hfxBd
    (inter_closure_sdiff_subset_boundaryComplex L B hL hB hBL ⟨hfxB, h⟩)
  have hBnhds : B.space ∈ 𝓝[L.space] f x := by
    refine mem_nhdsWithin.mpr ⟨(closure (L.space \ B.space))ᶜ, isClosed_closure.isOpen_compl,
      hnot, ?_⟩
    rintro y ⟨hy, hyL⟩
    by_contra hyB
    exact hy (subset_closure ⟨hyL, hyB⟩)
  exact Filter.mem_of_superset hBnhds hBQ

theorem IsPLHomeomorphOn.image_mem_nhdsWithin_of_isCombinatorialManifold
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (hK : IsCombinatorialManifold (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    {P : Set E} {Q : Set F} {f : E → F} (hf : IsPLHomeomorphOn f P Q)
    (hQL : Q ⊆ L.space) {x : E} (hx : x ∈ K.space)
    (hP : P ∈ 𝓝[K.space] x) : Q ∈ 𝓝[L.space] f x := by
  classical
  apply hf.image_mem_nhdsWithin_of_notMem_boundaryComplex K L
    hK.isCombinatorialManifoldWithBoundary hL hQL hx _ hP
  intro hxB
  obtain ⟨s, hs, _⟩ := (boundaryComplex (n + 1) K).mem_space_iff.mp hxB
  rw [hK.boundaryComplex_faces_eq_empty K] at hs
  exact hs.elim

end DifferentialGeometry.Topology.PiecewiseLinear
