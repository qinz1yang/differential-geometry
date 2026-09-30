/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismCapAdjustment
import DifferentialGeometry.Topology.PiecewiseLinear.HeightTriangleStability
import DifferentialGeometry.Topology.PiecewiseLinear.StandardTriangleCoordinates

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_prism_cap_images_preserving_stdCenter
    {C D₀ D₁ : Set (EuclideanSpace ℝ (Fin 3))}
    {ρ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hρ : IsPLHomeomorphOn ρ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) C)
    (hD₀ : D₀ ⊆ frontier C) (hD₁ : D₁ ⊆ frontier C) (hdis : Disjoint D₀ D₁)
    {r₀ r₁ : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hρ0 : ρ (stdCenter 1, 0) = r₀ (stdCenter 1))
    (hρ1 : ρ (stdCenter 1, 1) = r₁ (stdCenter 1)) :
    ∃ σ : (Fin 3 → ℝ) × ℝ → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn σ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) C ∧
      σ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)}) = D₀ ∧
      σ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(1 : ℝ)}) = D₁ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, σ (stdCenter 1, t) = ρ (stdCenter 1, t) := by
  let π : (Fin 3 → ℝ) → ℝ × ℝ := fun x => (x 1, x 2)
  let P : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}
  have hP : IsHPolytope P := isHPolytope_coordinate_triangle
  have hπ : IsPLHomeomorphOn π (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P :=
    isPLHomeomorphOn_triangle_coordinate_projection
  have hp : stdCenter 1 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
    openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 1)
  have hc : π (stdCenter 1) ∈ interior P := stdCenter_mem_interior_coordinate_triangle
  let φ := ρ ∘ Prod.map (Function.invFunOn π (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) (id : ℝ → ℝ)
  have hI : IsPLHomeomorphOn (id : ℝ → ℝ) (Icc 0 1) (Icc 0 1) :=
    isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  have hφ : IsPLHomeomorphOn φ (P ×ˢ Icc (0 : ℝ) 1) C :=
    (hπ.symm.prodMap hI).trans hρ
  have hφp (t : ℝ) : φ (π (stdCenter 1), t) = ρ (stdCenter 1, t) := by
    change ρ (Function.invFunOn π (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (π (stdCenter 1)), t) = _
    rw [hπ.bijOn.invOn_invFunOn.1 hp]
  obtain ⟨τ, hτ, hτ0, hτ1, hτp⟩ :=
    IsPLHomeomorphOn.exists_prism_cap_images_preserving_axis
      (by simp [Module.finrank_prod]) hP hπ hc hφ hD₀ hD₁ hdis hr₀ hr₁
      ((hφp 0).trans hρ0) ((hφp 1).trans hρ1)
  refine ⟨τ ∘ Prod.map π id, (hπ.prodMap hI).trans hτ, ?_, ?_, fun t ht => ?_⟩
  · rw [image_comp, prodMap_image_prod, hπ.image_eq, image_id]
    exact hτ0
  · rw [image_comp, prodMap_image_prod, hπ.image_eq, image_id]
    exact hτ1
  · change τ (π (stdCenter 1), t) = ρ (stdCenter 1, t)
    exact (hτp t ht).trans (hφp t)

end DifferentialGeometry.Topology.PiecewiseLinear
