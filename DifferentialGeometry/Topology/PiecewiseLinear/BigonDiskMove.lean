/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonCrosscutBypass
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePair

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_isPLHomeomorphOn_disk_bigon_move
    {Q A C : Set Plane} {a b c d p q : Plane} (hQ : IsPLBall 2 Q)
    (hA : Schoenflies.IsCrosscut (frontier Q) A a b)
    (hC : Schoenflies.IsCrosscut (frontier Q) C c d)
    (hAC : A ∩ C = {p, q}) (hpq : p ≠ q)
    (hpQ : p ∈ interior Q) (hqQ : q ∈ interior Q)
    (hcp : HasPLCurveCrossingOnAt univ A C p)
    (hcq : HasPLCurveCrossingOnAt univ A C q) :
    ∃ u : Plane → Plane, IsPLHomeomorphOn u Q Q ∧ EqOn u id (frontier Q) ∧
      Disjoint (u '' A) C := by
  obtain ⟨A', hA', hcross', hdisj⟩ :=
    exists_isCrosscut_disjoint_of_two_crossings hQ hA hC hAC hpq hpQ hqQ hcp hcq
  have hAs : IsPLBall 1 A := isPLBall_one_of_isArcBetween_of_isPolygonal hA.arc hA.polygonal
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hAs hA.arc
  obtain ⟨δ, hδ, hδ0, hδ1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hA' hcross'.arc
  have hsub : ∀ T : Set Plane, Schoenflies.IsCrosscut (frontier Q) T a b → T ⊆ Q := by
    intro T hT x hx
    by_cases he : x ∈ ({a, b} : Set Plane)
    · rcases he with rfl | rfl
      · exact hQ.isPolyhedron.isClosed.frontier_subset hT.left_mem
      · exact hQ.isPolyhedron.isClosed.frontier_subset hT.right_mem
    · exact interior_subset (hQ.interior_eq_inside_frontier.symm ▸ hT.sdiff_subset ⟨hx, he⟩)
  obtain ⟨r, hr⟩ := id hQ
  obtain ⟨u, hu, huf, huA⟩ := exists_isPLHomeomorphOn_map_crosscut_eqOn_boundary
    hr hr.image_stdSimplexBoundary hr hr.image_stdSimplexBoundary hγ (hsub A hA)
    (by rw [hγ0, hγ1]; exact hA.inter_eq) hδ (hsub A' hcross')
    (by rw [hδ0, hδ1]; exact hcross'.inter_eq)
    hQ.isPLSphere_frontier.isPolyhedron.isPLHomeomorphOn_id
    (by simp only [id_eq, hγ0, hδ0]) (by simp only [id_eq, hγ1, hδ1])
  exact ⟨u, hu, huf, huA.symm ▸ hdisj⟩

end DifferentialGeometry.Topology.PiecewiseLinear
