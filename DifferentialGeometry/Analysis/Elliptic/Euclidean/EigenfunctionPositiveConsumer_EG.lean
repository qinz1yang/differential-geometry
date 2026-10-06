import DifferentialGeometry.Analysis.Elliptic.Euclidean.EigenfunctionPositive_EG

/-!
# Consumer of `exists_positive_first_eigenfunction_EG` (S-W-EIG, G2)

The unit disk `D ⊂ ℝ²` carries a smooth positive first Dirichlet eigenfunction:
`-Δu = μ u`, `u > 0` on `D`, `u ∈ H¹₀(D)`, `μ ≥ 0`, `∫_D u² = 1` (`ρ = 1`, `W = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "D" => Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1

theorem exists_positive_dirichlet_eigenfunction_ball_EG :
    ∃ (u : EuclideanSpace ℝ (Fin 2) → ℝ) (μ : ℝ), DeGiorgi.MemW01p 2 u D ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u D ∧ (∀ x ∈ D, 0 < u x) ∧ 0 ≤ μ ∧ (∫ x in D, u x ^ 2) = 1 ∧
      ∀ x ∈ D, -Laplacian.laplacian u x = μ * u x := by
  obtain ⟨u, μ, hu0, hu, hpos, hμ, hN, hEq, -⟩ :=
    exists_positive_first_eigenfunction_EG (Ω := D)
      (U := Set.univ) Metric.isOpen_ball Metric.isBounded_ball
      (convex_ball _ _).isPreconnected ⟨0, Metric.mem_ball_self one_pos⟩ isOpen_univ
      (Set.subset_univ _) (ρ := fun _ => (1 : ℝ)) (W := fun _ => (0 : ℝ)) contDiffOn_const
      contDiffOn_const (fun _ _ => one_pos) (fun φ _ _ _ => by
        simp only [zero_mul, integral_zero, add_zero]
        exact integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
  refine ⟨u, μ, hu0, hu, hpos, hμ, by simpa using hN, fun x hx => ?_⟩
  have := hEq x hx
  simp only [zero_mul, add_zero] at this
  linarith

end DifferentialGeometry.Analysis.Sobolev.Euclidean
