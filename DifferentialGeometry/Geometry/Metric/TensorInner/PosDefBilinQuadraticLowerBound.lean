import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity

namespace DifferentialGeometry

theorem posDef_bilin_quadratic_lower_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hPD : ∀ v : F, v ≠ 0 → 0 < B v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : F, c * ‖v‖ ^ 2 ≤ B v v := by
  simpa only [IsCoercive, pow_two, mul_assoc] using B.isCoercive_of_posDef hPD

end DifferentialGeometry
