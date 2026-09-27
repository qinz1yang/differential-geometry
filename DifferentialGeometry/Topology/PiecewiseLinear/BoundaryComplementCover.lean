/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem boundaryComplex_space_of_closure_sdiff_of_boundary_subset {n : ℕ}
    (K A R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.space ⊆ K.space)
    (hR : IsCombinatorialManifoldWithBoundary (n + 1) R)
    (hRspace : R.space = closure (K.space \ A.space))
    (hbd : (boundaryComplex (n + 1) K).space ⊆ A.space) :
    (boundaryComplex (n + 1) R).space = R.space ∩ A.space := by
  apply Subset.antisymm
  · have heq := boundaryComplex_space_of_closure_sdiff K A R hK hA hAK hR hRspace
    rw [sdiff_eq_empty.mpr hbd, closure_empty, empty_union] at heq
    refine subset_inter (boundaryComplex_space_subset (n + 1) R) ?_
    rw [heq]
    exact closure_minimal (sdiff_subset.trans (boundaryComplex_space_subset (n + 1) A))
      (isPolyhedron_space A).isClosed
  · rw [inter_comm]
    exact inter_space_complement_subset_boundaryComplex K A R hK hA hAK hR hRspace

end DifferentialGeometry.Topology.PiecewiseLinear
