import DifferentialGeometry.Analysis.Elliptic.Euclidean.EigenfunctionComplexNorm_EG

/-!
# Consumer of `exists_positive_first_eigenfunction_complex_norm_EG` (S-W-EIG, G4)

For the unit disk in `ℂ` with `ρ = 1`, `W = 0`: the stability hypothesis in norm form
`0 ≤ ∫ ‖dφ‖²` holds trivially, and the theorem gives the positive first Dirichlet eigenfunction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "D" => Metric.ball (0 : ℂ) 1

theorem exists_positive_dirichlet_eigenfunction_norm_ball_EG :
    ∃ (u : ℂ → ℝ) (μ : ℝ), ContDiffOn ℝ (⊤ : ℕ∞) u D ∧ (∀ z ∈ D, 0 < u z) ∧ 0 ≤ μ ∧
      (∫ z in D, u z ^ 2) = 1 ∧ (∀ z ∈ D, -Laplacian.laplacian u z = μ * u z) := by
  obtain ⟨u, μ, hu, hpos, hμ, hN, hEq, -⟩ :=
    exists_positive_first_eigenfunction_complex_norm_EG (Ω := D) (U := Set.univ)
      Metric.isOpen_ball Metric.isBounded_ball (convex_ball _ _).isPreconnected
      ⟨0, Metric.mem_ball_self one_pos⟩ isOpen_univ (Set.subset_univ _)
      (ρ := fun _ => (1 : ℝ)) (W := fun _ => (0 : ℝ)) contDiffOn_const contDiffOn_const
      (fun _ _ => one_pos) (fun φ _ _ _ => by
        simp only [zero_mul, add_zero]
        exact integral_nonneg fun x => sq_nonneg _)
  refine ⟨u, μ, hu, hpos, hμ, by simpa using hN, fun z hz => ?_⟩
  have := hEq z hz
  simp only [zero_mul, add_zero] at this
  linarith

end DifferentialGeometry.Analysis.Sobolev.Euclidean
