/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homeomorph.Conjugate
import DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
import DifferentialGeometry.Topology.PiecewiseLinear.ChartTameNestedCells

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.image_conjugateHomeomorph {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {d : ℕ} {S B : Set M}
    (hS : IsPLCellOn d S B) {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) (hSc : S ⊆ c.source)
    (Φ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
    (hΦ : IsPLHomeomorphOn Φ univ univ) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ c.target) (hfix : EqOn Φ id Kᶜ) :
    IsPLCellOn d ((c.conjugateHomeomorph Φ hK hKc hfix) '' S)
      ((c.conjugateHomeomorph Φ hK hKc hfix) '' B) := by
  have hmaps : MapsTo Φ c.target c.target := by
    intro x hx
    by_contra hn
    have hnK : Φ x ∉ K := fun hxK => hn (hKc hxK)
    have heq : Φ x = x := Φ.injective (hfix hnK)
    exact hn (by rwa [heq])
  obtain ⟨q, hq, hB⟩ := hS.exists_isPLHomeomorphOn_image_chart hc hSc
  have hball : IsPLBall d (c '' S) := ⟨q, hq⟩
  have hr := hq.trans (hΦ.restrict hball.isPolyhedron (subset_univ _))
  have hR : IsPolyhedron (Φ '' (c '' S)) := (IsPLBall.isPolyhedron ⟨Φ ∘ q, hr⟩)
  have hRc : Φ '' (c '' S) ⊆ c.target := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hmaps (c.map_source (hSc hx))
  have himg : ∀ A ⊆ S,
      (c.conjugateHomeomorph Φ hK hKc hfix) '' A = c.symm '' (Φ '' (c '' A)) := by
    intro A hAS
    rw [← image_comp, ← image_comp]
    apply image_congr
    intro x hx
    exact c.conjugateMap_of_mem Φ (hSc (hAS hx))
  refine ⟨Φ '' (c '' S), Φ ∘ q, c.symm, hr,
    isPLHomeomorphInto_symm_of_mem_maximalAtlas hc hR hRc, himg S Subset.rfl, ?_⟩
  rw [himg B hS.boundary_subset, image_comp, ← hB]

end DifferentialGeometry.Topology.PiecewiseLinear
