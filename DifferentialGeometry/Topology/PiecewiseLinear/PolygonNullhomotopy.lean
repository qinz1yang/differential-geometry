/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homotopy.CyclicLoopMap
import DifferentialGeometry.Topology.Homotopy.FreeLoopNullhomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonCircleParametrization
import Mathlib.Analysis.Convex.PathConnected

/-! Nullhomotopic spanning polygonal cycles annihilate every loop. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]

open Classical in
theorem isPathConnected_space_of_spanning_cycle
    (hK : IsCombinatorialManifold 1 K) {v : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v v) (hcyc : γ.IsCycle)
    (hspan : γ.toSubgraph.verts = univ) : IsPathConnected K.space := by
  have heq : K.space = pathCarrier (arcPath γ) := Subset.antisymm
    (space_subset_arcCarrier hK γ hcyc hspan) (pathCarrier_subset_space _)
  let _ : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, le_rfl, zero_le_one⟩)
  rw [heq]
  exact isPathConnected_range (continuous_subtype_val.comp (arcPath γ).continuous)

open Classical in
theorem map_homotopic_refl_of_nullhomotopic_spanning_cycle
    {X : Type*} [TopologicalSpace X] (hK : IsCombinatorialManifold 1 K)
    {v : K.vertices} (γ : (SimplicialComplex.edgeGraph K).Walk v v) (hcyc : γ.IsCycle)
    (hspan : γ.toSubgraph.verts = univ) (f : C(K.space, X))
    (hnull : (pathToCircle ((walkPath γ).map f.continuous)).Nullhomotopic)
    (y : K.space) (q : Path y y) :
    (q.map f.continuous).Homotopic (Path.refl (f y)) := by
  let _ : PathConnectedSpace K.space := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_space_of_spanning_cycle hK γ hcyc hspan)
  exact map_homotopic_refl_of_generating_loop f
    (exists_homotopic_loopZPow_walkPath hK γ hcyc hspan)
    ((pathToCircle_nullhomotopic_iff _).mp hnull)
    ⟨PathConnectedSpace.somePath _ y⟩ q

end DifferentialGeometry.Topology.PiecewiseLinear
