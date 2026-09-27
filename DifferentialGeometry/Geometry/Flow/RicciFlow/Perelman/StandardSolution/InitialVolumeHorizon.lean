import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVolumeLower

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Geometry.Riemannian
namespace DifferentialGeometry.PDE.RicciFlow

theorem initialReducedVolumeLowerCoeff_antitoneOn (n : ℕ) (K c : ℝ)
    (hK : 0 < K) (hc : 0 < c) :
    AntitoneOn (fun H : ℝ ↦ initialReducedVolumeLowerCoeff n H K c) (Ioi 0) := by
  have hr : 0 ≤ min (c / 2) (intrinsicNormalMetricRadius n K) :=
    (lt_min (half_pos hc) (intrinsicNormalMetricRadius_pos n K hK.le)).le
  intro H₁ hH₁ H₂ _hH₂ hH
  change 0 < H₁ at hH₁
  have hG : (4 * Real.pi * H₂) ^ (-(n : ℝ) / 2) ≤
      (4 * Real.pi * H₁) ^ (-(n : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 4 * Real.pi * H₁)
      (mul_le_mul_of_nonneg_left hH (by positivity))
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
  unfold initialReducedVolumeLowerCoeff
  apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left ?_ (intrinsicBallVolumeCoeff_pos n).le
  apply min_le_min ?_ le_rfl
  exact mul_le_mul_of_nonneg_left hG (pow_nonneg hr n)

end DifferentialGeometry.PDE.RicciFlow
end
