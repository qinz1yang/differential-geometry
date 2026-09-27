/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import DifferentialGeometry.Topology.PiecewiseLinear.TorusCircleHomology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_maximal_firstHomology_image_of_disjoint_polygons {S : Set E3}
    (hS : IsCombinatorialSolidTorus S) {n : ℕ} (G : Fin (n + 1) → Set E3)
    (hG : ∀ i, IsPLSphere 1 (G i)) (hGS : ∀ i, G i ⊆ frontier S)
    (hGT : ∀ i, G i ⊆ S) (hdisj : Pairwise (fun i j => Disjoint (G i) (G j))) :
    ∃ i, ∀ j,
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion (hGT j), continuous_inclusion (hGT j)⟩ : C(G j, S))) ≤
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion (hGT i), continuous_inclusion (hGT i)⟩ : C(G i, S))) := by
  classical
  let Θ := frontier S
  have hΘ : IsPLTorus Θ := hS.isPLTorus_frontier
  have hΘS : Θ ⊆ S := hS.isPolyhedron.isClosed.frontier_subset
  have hImageΘ : id '' Θ ⊆ S := by simpa only [Set.image_id] using hΘS
  have hImageG (i : Fin (n + 1)) : id '' G i ⊆ S :=
    (image_mono (hGS i)).trans hImageΘ
  have range_eq_of_eq {A B : Set E3} (hAB : A = B)
      (hAS : A ⊆ S) (hBS : B ⊆ S) :
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion hAS, continuous_inclusion hAS⟩ : C(A, S))) =
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion hBS, continuous_inclusion hBS⟩ : C(B, S))) := by
    subst B
    rfl
  have hmap (i : Fin (n + 1)) :
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion (hImageG i), continuous_inclusion (hImageG i)⟩ : C(id '' G i, S))) =
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion (hGT i), continuous_inclusion (hGT i)⟩ : C(G i, S))) := by
    exact range_eq_of_eq (Set.image_id (G i)) (hImageG i) (hGT i)
  by_cases hex : ∃ i, IsPreconnected (Θ \ G i)
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, fun j => ?_⟩
    by_cases hij : j = i
    · subst hij
      exact le_rfl
    by_cases hj : IsPreconnected (Θ \ G j)
    · have heq := hΘ.range_integralSingularHomologyMap_eq_of_disjoint
        (hG j) (hGS j) (hG i) (hGS i) (hdisj (fun h => hij h.symm)) hj hi
        (φ := id) (S := S) continuousOn_id (fun _ _ _ _ h => h)
        hImageΘ
      change LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion (hImageG j), continuous_inclusion (hImageG j)⟩ : C(id '' G j, S))) =
        LinearMap.range (integralSingularHomologyMap 1
          (⟨inclusion (hImageG i), continuous_inclusion (hImageG i)⟩ : C(id '' G i, S))) at heq
      rw [hmap j, hmap i] at heq
      exact heq.le
    · have hbot := hΘ.range_integralSingularHomologyMap_eq_bot_of_not_isPreconnected
        (hG j) (hGS j) hj (φ := id) (S := S) continuousOn_id
        (fun _ _ _ _ h => h) hImageΘ
      change LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion (hImageG j), continuous_inclusion (hImageG j)⟩ : C(id '' G j, S))) =
        (⊥ : Submodule ℤ (integralSingularHomology 1 S)) at hbot
      rw [hmap j] at hbot
      exact hbot.le.trans bot_le
  · refine ⟨0, fun j => ?_⟩
    have hbot := hΘ.range_integralSingularHomologyMap_eq_bot_of_not_isPreconnected
      (hG j) (hGS j) (fun hj => hex ⟨j, hj⟩) (φ := id) (S := S)
      continuousOn_id (fun _ _ _ _ h => h) hImageΘ
    change LinearMap.range (integralSingularHomologyMap 1
      (⟨inclusion (hImageG j), continuous_inclusion (hImageG j)⟩ : C(id '' G j, S))) =
      (⊥ : Submodule ℤ (integralSingularHomology 1 S)) at hbot
    rw [hmap j] at hbot
    exact hbot.le.trans bot_le

end DifferentialGeometry.Topology.PiecewiseLinear
