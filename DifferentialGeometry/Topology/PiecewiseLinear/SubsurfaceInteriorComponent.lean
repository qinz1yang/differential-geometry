/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorConnected

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.connectedComponentIn_sdiff_boundaryComplex_eq
    [d : DecidableEq E] {n : ℕ}
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary (n + 1) R)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hconn : IsPreconnected R.space) (hRK : R.space ⊆ K.space)
    (hdis : Disjoint R.space (boundaryComplex (n + 1) K).space)
    {x : E} (hx : x ∈ R.space \ (boundaryComplex (n + 1) R).space) :
    connectedComponentIn (K.space \ (boundaryComplex (n + 1) R).space) x =
      R.space \ (boundaryComplex (n + 1) R).space := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  have hmeet := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K R hK hR hRK hdis
  let C := connectedComponentIn (K.space \ (boundaryComplex (n + 1) R).space) x
  have hCsub : C ⊆ K.space \ (boundaryComplex (n + 1) R).space :=
    connectedComponentIn_subset _ _
  have hcover : C ⊆ R.space ∪ closure (K.space \ R.space) := by
    intro y hy
    by_cases hyR : y ∈ R.space
    · exact Or.inl hyR
    · exact Or.inr (subset_closure ⟨(hCsub hy).1, hyR⟩)
  have hempty : C ∩ (R.space ∩ closure (K.space \ R.space)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact (hCsub hy.1).2 (hmeet.subset hy.2)
  have hCR : C ⊆ R.space := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_connectedComponentIn
        R.space (closure (K.space \ R.space)) (isPolyhedron_space R).isClosed isClosed_closure
        hcover hempty with hin | hout
    · exact hin
    · exact (hx.2 (hmeet.subset ⟨hx.1, hout (mem_connectedComponentIn ⟨hRK hx.1, hx.2⟩)⟩)).elim
  refine Subset.antisymm (fun y hy => ⟨hCR hy, (hCsub hy).2⟩) ?_
  exact (hR.isPreconnected_sdiff_boundaryComplex_space hconn).subset_connectedComponentIn hx
    (fun y hy => ⟨hRK hy.1, hy.2⟩)

theorem IsCombinatorialManifoldWithBoundary.closure_connectedComponentIn_sdiff_boundaryComplex_eq
    [DecidableEq E] {n : ℕ}
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary (n + 1) R)
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hconn : IsPreconnected R.space) (hRK : R.space ⊆ K.space)
    (hdis : Disjoint R.space (boundaryComplex (n + 1) K).space)
    {x : E} (hx : x ∈ R.space \ (boundaryComplex (n + 1) R).space) :
    closure (connectedComponentIn (K.space \ (boundaryComplex (n + 1) R).space) x) = R.space := by
  rw [hR.connectedComponentIn_sdiff_boundaryComplex_eq K R hK hconn hRK hdis hx]
  exact Subset.antisymm (closure_minimal sdiff_subset (isPolyhedron_space R).isClosed)
    hR.space_subset_closure_sdiff_boundaryComplex_space

end DifferentialGeometry.Topology.PiecewiseLinear
