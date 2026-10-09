/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TubeCenteredPrismCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3}

open Classical in
theorem IsTube.isPLBall_dualCell_pair (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces) : IsPLBall 3 (C u ∪ C v) := by
  obtain ⟨ρ, hρ, -⟩ := ht.exists_centered_prism_coordinates hu hv huv he
  exact (isPLBall_three_prod (isPLBall_stdSimplex 2)
    (isPLBall_Icc (by norm_num : (-1 : ℝ) < 1))).of_isPLHomeomorphOn hρ

theorem IsTube.mem_interior_image_dualCell (ht : IsTube K N C D Dbd h N')
    (hv : v ∈ K.vertices) : h v ∈ interior (h '' C v) := by
  rw [interior_image_eq_image_interior_of_isCompact (ht.dualBall v hv).isPolyhedron.isCompact
    (ht.continuousOn.mono (ht.dualCell_subset hv)) (ht.injOn.mono (ht.dualCell_subset hv))]
  exact ⟨v, ht.mem_interior_dualCell hv, rfl⟩

open Classical in
theorem IsTube.isConnected_interior_image_pair (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces) :
    IsConnected (interior (h '' C u ∪ h '' C v)) := by
  have hball := ht.isPLBall_dualCell_pair hu hv huv he
  have hsub : C u ∪ C v ⊆ N := union_subset (ht.dualCell_subset hu) (ht.dualCell_subset hv)
  rw [← image_union, interior_image_eq_image_interior_of_isCompact hball.isPolyhedron.isCompact
    (ht.continuousOn.mono hsub) (ht.injOn.mono hsub)]
  exact (hball.isConnected_interior_of_finrank (by simp)).image h
    (ht.continuousOn.mono (interior_subset.trans hsub))

end DifferentialGeometry.Topology.PiecewiseLinear
