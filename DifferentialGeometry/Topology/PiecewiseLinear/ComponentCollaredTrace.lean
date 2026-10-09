/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplement
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasFiniteCollaredTrace.of_connected_component
    (K : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] {T : Set E3}
    (h : HasFiniteCollaredTrace K.space T) (c : ConnectedComponents K.space) :
    HasFiniteCollaredTrace (connectedComponentComplex K c).space T := by
  classical
  let _ : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  have hsub : (connectedComponentComplex K c).space ⊆ K.space :=
    (subset_iUnion (fun d => (connectedComponentComplex K d).space) c).trans
      (iUnion_connectedComponentComplex_space K).subset
  have hcover : (connectedComponentComplex K c).space ∪
      (K.space \ (connectedComponentComplex K c).space) = K.space := by
    refine Subset.antisymm (union_subset hsub sdiff_subset) ?_
    intro x hx
    by_cases hxc : x ∈ (connectedComponentComplex K c).space
    · exact Or.inl hxc
    · exact Or.inr ⟨hx, hxc⟩
  have hwhole : HasFiniteCollaredTrace ((connectedComponentComplex K c).space ∪
      (K.space \ (connectedComponentComplex K c).space)) T := hcover.symm ▸ h
  exact hwhole.of_disjoint_union_left (isPolyhedron_space (connectedComponentComplex K c))
    (isPolyhedron_sdiff_connectedComponentComplex K c).isClosed
    (disjoint_left.mpr fun _ hx hy => hy.2 hx)

end DifferentialGeometry.Topology.PiecewiseLinear
