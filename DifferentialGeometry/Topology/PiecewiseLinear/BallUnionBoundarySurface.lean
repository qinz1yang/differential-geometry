/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.LocalSurfaceLink

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_combinatorial_surface_frontier_iUnion {ι : Type*} [Finite ι] {B : ι → Set E3}
    (hB : ∀ i, IsPLBall 3 (B i))
    (hD : ∀ i j, i ≠ j → (B i ∩ B j).Nonempty →
      IsPLBall 2 (B i ∩ B j) ∧ B i ∩ B j ⊆ frontier (B i))
    (h3 : ∀ i j k, i ≠ j → k ≠ i → k ≠ j → Disjoint (B i ∩ B j) (B k)) :
    ∃ L : Geometry.SimplicialComplex ℝ E3, L.faces.Finite ∧
      IsCombinatorialManifold 2 L ∧ L.space = frontier (⋃ i, B i) := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  have hP : IsPolyhedron (⋃ i, B i) := IsPolyhedron.iUnion fun i => (hB i).isPolyhedron
  obtain ⟨L, hLfin, hLspace⟩ := hP.frontier.exists_simplicialComplex
  have : Finite L.faces := hLfin.to_subtype
  refine ⟨L, hLfin, ?_, hLspace⟩
  intro v hv
  have hvL : v ∈ L.space := L.convexHull_subset_space hv (subset_convexHull ℝ _ (by simp))
  have hvF := hLspace.subset hvL
  obtain ⟨O, hO, hvO, S, hS, hOS⟩ :=
    exists_isOpen_inter_frontier_iUnion_eq_isPLSphere hB hD h3 hvF
  have hvS : v ∈ S := (hOS.subset ⟨hvO, hvF⟩).2
  obtain ⟨W, hW, hvW, U, hU, ⟨ψ⟩⟩ := exists_isOpen_inter_homeomorph_of_inter_eq hO hOS hvO
    (hS.exists_isOpen_inter_homeomorph_of_two hvS)
  apply isPLSphere_one_geometricLink_of_homeomorph L hU ψ hv
  filter_upwards [hW.mem_nhds hvW] with y hy
  rw [hLspace]
  exact ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
