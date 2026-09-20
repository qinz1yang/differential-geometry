import DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzW1


namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

open scoped NNReal

variable {d : ℕ}

theorem exists_lipschitzWith_of_locallyLipschitz_hasCompactSupport
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : LocallyLipschitz u) (huc : HasCompactSupport u) :
    ∃ C : ℝ≥0, LipschitzWith C u := by
  obtain ⟨B₀, hB₀⟩ := huc.exists_bound_of_continuous hu.continuous
  let B : ℝ≥0 := ⟨max B₀ 0, le_max_right _ _⟩
  have hB : ∀ x, edist (u x) 0 ≤ B := by
    intro x
    rw [edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_le_coe]
    exact_mod_cast (hB₀ x).trans (le_max_left B₀ 0)
  exact lip_of_local_comp hu huc hB

end DifferentialGeometry.Analysis.Sobolev.Euclidean
