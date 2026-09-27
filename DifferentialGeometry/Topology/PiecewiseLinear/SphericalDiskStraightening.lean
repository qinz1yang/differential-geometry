/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexDiskStraightening

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLSphere.exists_ambient_isPLHomeomorphOn_disk_to_simplex
    {S D : Set E3} (hS : IsPLSphere 2 S) (hD : IsPLBall 2 D) (hDS : D ⊆ S) :
    ∃ (T : Finset E3) (a : E3) (f : E3 ≃ₜ E3),
      AffineIndependent ℝ ((↑) : T → E3) ∧ T.card = 4 ∧ a ∈ T ∧
      IsPLHomeomorphOn f univ univ ∧
      f '' S = frontier (convexHull ℝ (T : Set E3)) ∧
      f '' D = convexHull ℝ (T.erase a : Set E3) := by
  classical
  obtain ⟨T, g, hT, hcard, hg, hgS, -⟩ :=
    hS.isSimplyEmbedded.2 univ convex_univ isOpen_univ (subset_univ S)
  have hgD := hD.of_isPLHomeomorphOn (hg.restrict hD.isPolyhedron (subset_univ D))
  have hgDS : g '' D ⊆ frontier (convexHull ℝ (T : Set E3)) :=
    (image_mono hDS).trans hgS.le
  obtain ⟨a, ha, k, hk, hkT, hkD, -⟩ :=
    exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron T hT hcard hgD hgDS
      isOpen_univ (subset_univ _)
  refine ⟨T, a, g.trans k, hT, hcard, ha, hg.trans hk, ?_, ?_⟩
  · change (k ∘ g) '' S = _
    rw [image_comp, hgS, k.image_frontier, hkT]
  · change (k ∘ g) '' D = _
    rw [image_comp, hkD]

theorem IsPLBall.exists_ambient_isPLHomeomorphOn_disk_to_simplex
    {B D : Set E3} (hB : IsPLBall 3 B) (hD : IsPLBall 2 D)
    (hDB : D ⊆ frontier B) :
    ∃ (T : Finset E3) (a : E3) (f : E3 ≃ₜ E3),
      AffineIndependent ℝ ((↑) : T → E3) ∧ T.card = 4 ∧ a ∈ T ∧
      IsPLHomeomorphOn f univ univ ∧ f '' B = convexHull ℝ (T : Set E3) ∧
      f '' D = convexHull ℝ (T.erase a : Set E3) := by
  obtain ⟨T, a, f, hT, hcard, ha, hf, hfS, hfD⟩ :=
    hB.isPLSphere_frontier.exists_ambient_isPLHomeomorphOn_disk_to_simplex hD hDB
  refine ⟨T, a, f, hT, hcard, ha, hf, ?_, hfD⟩
  have hfront : frontier (f '' B) = frontier (convexHull ℝ (T : Set E3)) := by
    rw [← f.image_frontier, hfS]
  have hint : (interior (f '' B)).Nonempty := by
    rw [← f.image_interior]
    exact hB.interior_nonempty.image f
  exact DifferentialGeometry.Analysis.IsCompact.eq_of_frontier_eq_convex_closed
    (hB.isPolyhedron.isCompact.image f.continuous) hint (convex_convexHull ℝ _)
    ((hasPushProperty_convexHull_simplex T hT hcard).1.isPolyhedron.isCompact.isClosed) hfront

end DifferentialGeometry.Topology.PiecewiseLinear
