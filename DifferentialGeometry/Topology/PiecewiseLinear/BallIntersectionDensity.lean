/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorDensity

/-! Density of the complement of lower-dimensional intersections of PL balls. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.subset_closure_sdiff_iUnion_of_isPLBall_inter
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {A : Set E} (hA : IsPLBall (n + 1) A) (hAK : A ⊆ K.space)
    {ι : Type*} (D : ι → Set E) (hD : ∀ i, IsPLBall (n + 1) (D i))
    (hDK : ∀ i, D i ⊆ K.space) (hI : ∀ i, IsPLBall n (A ∩ D i)) :
    A ⊆ closure (K.space \ ⋃ i, D i) := by
  classical
  obtain ⟨L, hfin, hspace⟩ := hA.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hfin.to_subtype
  have hL : IsPLBall (n + 1) L.space := hspace.symm ▸ hA
  have hLman := hL.isCombinatorialManifoldWithBoundary
  have hdense := hLman.space_subset_closure_sdiff_boundaryComplex_space
  rw [hspace] at hdense
  apply hdense.trans (closure_mono ?_)
  rintro x ⟨hxA, hxB⟩
  refine ⟨hAK hxA, ?_⟩
  intro hxD
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
  apply hxB
  exact hK.inter_subset_boundaryComplex_of_isPLBall L hL
    (hspace.symm ▸ hAK) (hD i) (hDK i) (hspace.symm ▸ hI i) ⟨hspace.symm ▸ hxA, hxi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
