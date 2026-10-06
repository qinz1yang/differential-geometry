import DifferentialGeometry.Analysis.Elliptic.Euclidean.EigenfunctionComplex_EG

/-!
# Consumer of `exists_positive_first_eigenfunction_complex_EG` (S-W-EIG, G3)

The unit disk `D ⊂ ℂ` has a smooth positive first Dirichlet eigenfunction `-Δu = μ u`, `μ ≥ 0`,
`∫_D u² = 1`, with `μ ∫ φ² ≤ ∫ |∇φ|²` for every `φ ∈ C_c^∞(D)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "D" => Metric.ball (0 : ℂ) 1

theorem exists_positive_dirichlet_eigenfunction_complex_ball_EG :
    ∃ (u : ℂ → ℝ) (μ : ℝ), ContDiffOn ℝ (⊤ : ℕ∞) u D ∧ (∀ z ∈ D, 0 < u z) ∧ 0 ≤ μ ∧
      (∫ z in D, u z ^ 2) = 1 ∧ (∀ z ∈ D, -Laplacian.laplacian u z = μ * u z) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ D →
        μ * (∫ z in D, φ z ^ 2) ≤
          ∫ z in D, ((fderiv ℝ φ z 1) ^ 2 + (fderiv ℝ φ z Complex.I) ^ 2) := by
  obtain ⟨u, μ, hu, hpos, hμ, hN, hEq, hmin⟩ :=
    exists_positive_first_eigenfunction_complex_EG (Ω := D) (U := Set.univ)
      Metric.isOpen_ball Metric.isBounded_ball (convex_ball _ _).isPreconnected
      ⟨0, Metric.mem_ball_self one_pos⟩ isOpen_univ (Set.subset_univ _)
      (ρ := fun _ => (1 : ℝ)) (W := fun _ => (0 : ℝ)) contDiffOn_const contDiffOn_const
      (fun _ _ => one_pos) (fun φ _ _ _ => by
        simp only [zero_mul, integral_zero, add_zero]
        exact integral_nonneg fun x => add_nonneg (sq_nonneg _) (sq_nonneg _))
  refine ⟨u, μ, hu, hpos, hμ, by simpa using hN, fun z hz => ?_, fun φ h1 h2 h3 => ?_⟩
  · have := hEq z hz
    simp only [zero_mul, add_zero] at this
    linarith
  · have := hmin φ h1 h2 h3
    simpa using this

end DifferentialGeometry.Analysis.Sobolev.Euclidean
