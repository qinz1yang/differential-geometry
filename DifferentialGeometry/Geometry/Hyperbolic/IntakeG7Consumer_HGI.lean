import DifferentialGeometry.Geometry.Hyperbolic.TruncationStability

/-!
# Consumer of the G7 intake (S-HG-INTAKE, suffix `_HGI`)

HG06 in the single-pair form `∃ ξ n` (ch12 D-R3-19): from the donor theorem
`exists_isometry_close_of_truncation_count_le` we read off the pair `(ξ, n)` with `ξ = 1/(n+1)`
and `η⁻¹ < ξ⁻¹`.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u

theorem hg06_pair_exists_HGI (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) {η : ℝ}
    (hη : 0 < η) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ := by
  obtain ⟨ξ, hξ, n, hn, hr, -⟩ :=
    FiniteVolumeHyperbolicModel.exists_isometry_close_of_truncation_count_le.{u, 0} H o hη
  exact ⟨ξ, hξ, n, hn, hr⟩

end DifferentialGeometry.Geometry.Hyperbolic
