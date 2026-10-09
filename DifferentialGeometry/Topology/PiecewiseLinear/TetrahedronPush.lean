/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexDiskStraightening

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem hasPushProperty_convexHull_simplex
    (T : Finset (EuclideanSpace ℝ (Fin 3)))
    (hT : AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 3))) (hcard : T.card = 4) :
    HasPushProperty (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) := by
  refine ⟨isPLBall_convexHull_of_affineIndependent T hT hcard, ?_⟩
  intro D hD hDC
  obtain ⟨a, ha, h, hh, hC, hDh, -⟩ :=
    exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron T hT hcard hD hDC isOpen_univ
        (subset_univ _)
  have hF : AffineIndependent ℝ ((↑) : T.erase a → EuclideanSpace ℝ (Fin 3)) :=
    affineIndependent_of_subset hT (Finset.erase_subset a T)
  have hFcard : (T.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, hcard]
  have hTa : AffineIndependent ℝ ((↑) : ↥(insert a (T.erase a) : Finset _) → EuclideanSpace ℝ (Fin
      3)) := by
    rw [Finset.insert_erase ha]
    exact hT
  have hface := hasPushPropertyAt_convexHull_simplex_face (T.erase a) hF hFcard
    (Finset.notMem_erase a T) hTa
  have hface' : HasPushPropertyAt (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) (h '' D) := by
    rw [hDh]
    simpa only [Finset.insert_erase ha] using hface
  have hinvC : h.symm '' convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) =
      convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) := by
    calc
      h.symm '' convexHull ℝ (T : Set _) = h.symm '' (h '' convexHull ℝ (T : Set _)) :=
        congrArg (Set.image h.symm) hC.symm
      _ = _ := by rw [h.image_symm, h.injective.preimage_image]
  have hinvD : h.symm '' (h '' D) = D := by rw [h.image_symm, h.injective.preimage_image]
  have hback := hface'.image hh.homeomorph_symm
  rwa [hinvC, hinvD] at hback

end DifferentialGeometry.Topology.PiecewiseLinear
