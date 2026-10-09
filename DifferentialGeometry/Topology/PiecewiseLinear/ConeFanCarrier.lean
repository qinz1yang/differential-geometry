/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeFan
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialApproximation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_isPiecewiseAffineOn_stdCone_fan_carrierFace {M N : ℕ} {u σ : ℕ → ℝ}
    {L : Geometry.SimplicialComplex ℝ F} (f : ℝ × ℝ → F) (w : ℕ → ℕ → F)
    (hu0 : u 0 = 0) (huM : u (M + 1) = 1) (humono : ∀ j ≤ M, u j < u (j + 1))
    (hσ0 : σ 0 = 0) (hσN : σ (N + 1) = 1) (hσmono : ∀ k ≤ N, σ k < σ (k + 1))
    (hw0 : ∀ j, w 0 j = w 0 0)
    (hstar : ∀ k ≤ N, ∀ j ≤ M, ∀ z ∈ stdCone, σ k ≤ z.1 + z.2 → z.1 + z.2 ≤ σ (k + 1) →
      z ∈ stdConeSector (u j) (u (j + 1)) →
      f z ∈ openStar L (w k j) ∧ f z ∈ openStar L (w k (j + 1)) ∧
        f z ∈ openStar L (w (k + 1) j) ∧ f z ∈ openStar L (w (k + 1) (j + 1))) :
    ∃ Ψ : ℝ × ℝ → F, IsPiecewiseAffineOn Ψ stdCone ∧ Ψ (0, 0) = w 0 0 ∧
      (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
        Ψ (t * (1 - u 0), t * u 0) =
          AffineMap.lineMap (w k 0) (w (k + 1) 0) ((t - σ k) / (σ (k + 1) - σ k))) ∧
      (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
        Ψ (t * (1 - u (M + 1)), t * u (M + 1)) =
          AffineMap.lineMap (w k (M + 1)) (w (k + 1) (M + 1))
            ((t - σ k) / (σ (k + 1) - σ k))) ∧
      (∀ j ≤ M, ∀ r ∈ Icc (u j) (u (j + 1)),
        Ψ (1 - r, r) =
          AffineMap.lineMap (w (N + 1) j) (w (N + 1) (j + 1)) ((r - u j) / (u (j + 1) - u j))) ∧
      (∀ z ∈ stdCone, Ψ z ∈ convexHull ℝ (carrierFace L (f z))) ∧
      MapsTo Ψ stdCone L.space := by
  obtain ⟨Ψ, hPA, hapex, hray₁, hray₂, houter, himg⟩ :=
    exists_isPiecewiseAffineOn_stdCone_fan w hu0 huM humono hσ0 hσN hσmono hw0
  have hcarrier : ∀ z ∈ stdCone, Ψ z ∈ convexHull ℝ (carrierFace L (f z)) := by
    intro z hz
    obtain ⟨k, hk, j, hj, h1, h2, hsec, hmem⟩ := himg z hz
    obtain ⟨s₁, s₂, s₃, s₄⟩ := hstar k hk j hj z hz h1 h2 hsec
    refine convexHull_min ?_ (convex_convexHull ℝ _) hmem
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact subset_convexHull ℝ _ (mem_carrierFace_of_mem_openStar L s₁)
    · exact subset_convexHull ℝ _ (mem_carrierFace_of_mem_openStar L s₂)
    · exact subset_convexHull ℝ _ (mem_carrierFace_of_mem_openStar L s₃)
    · exact subset_convexHull ℝ _ (mem_carrierFace_of_mem_openStar L s₄)
  refine ⟨Ψ, hPA, hapex, hray₁, hray₂, houter, hcarrier, ?_⟩
  intro z hz
  obtain ⟨k, hk, j, hj, h1, h2, hsec, -⟩ := himg z hz
  obtain ⟨s₁, -, -, -⟩ := hstar k hk j hj z hz h1 h2 hsec
  exact L.mem_space_iff.mpr ⟨carrierFace L (f z), carrierFace_mem s₁.1, hcarrier z hz⟩

end DifferentialGeometry.Topology.PiecewiseLinear
