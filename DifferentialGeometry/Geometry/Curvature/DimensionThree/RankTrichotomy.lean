import DifferentialGeometry.Geometry.Curvature.DimensionThree.PinchingAlgebra

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Curvature

theorem curvatureReactionSumSquares3_ordered_rank_trichotomy
    (lambda mu nu : Real)
    (hnu_nonneg : 0 ≤ nu)
    (hord : nu ≤ mu ∧ mu ≤ lambda)
    (hreaction : curvatureReactionSumSquares3 lambda mu nu = 0) :
    (lambda = 0 ∧ mu = 0 ∧ nu = 0) ∨
      (0 < lambda ∧ mu = 0 ∧ nu = 0) ∨
      (0 < nu ∧ lambda = mu ∧ mu = nu) := by
  by_cases hnu : 0 < nu
  · have hlambda : 0 < lambda := lt_of_lt_of_le hnu (le_trans hord.1 hord.2)
    have hrigid := (curvatureReactionSumSquares3_eq_zero_iff
      lambda mu nu hlambda hnu).mp hreaction
    exact Or.inr (Or.inr ⟨hnu, hrigid.1, hrigid.2⟩)
  · have hnu_zero : nu = 0 := le_antisymm (le_of_not_gt hnu) hnu_nonneg
    have hmu_nonneg : 0 ≤ mu := by linarith [hord.1]
    by_cases hmu : 0 < mu
    · have hlambda : 0 < lambda := lt_of_lt_of_le hmu hord.2
      have hpositive : 0 < lambda ^ 2 * (mu - nu) ^ 2 := by
        rw [hnu_zero]
        positivity
      have hrest : 0 ≤
          mu ^ 2 * (lambda - nu) ^ 2 + nu ^ 2 * (lambda - mu) ^ 2 := by
        positivity
      unfold curvatureReactionSumSquares3 at hreaction
      nlinarith
    · have hmu_zero : mu = 0 := le_antisymm (le_of_not_gt hmu) hmu_nonneg
      have hlambda_nonneg : 0 ≤ lambda := by linarith [hord.2]
      by_cases hlambda : 0 < lambda
      · exact Or.inr (Or.inl ⟨hlambda, hmu_zero, hnu_zero⟩)
      · have hlambda_zero : lambda = 0 := le_antisymm
          (le_of_not_gt hlambda) hlambda_nonneg
        exact Or.inl ⟨hlambda_zero, hmu_zero, hnu_zero⟩

end DifferentialGeometry.Geometry.Curvature
