import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Cover
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Shell

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem kochLammFluxShell_norm {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KochLammSourceOne T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    ‖kochLammFluxPiece1 R w f x (kochLammLateShell x R k)‖ ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
        (‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2) *
          (kochLammFluxTailC V * (Aₚ : ℝ))) := by
  have hnorm := kochLammFluxCover_norm (V := V) h w x hR
    (Nat.cast_nonneg k) hRT s (kochLammLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (kochLammLateShell_sub (V := V) x R k hy))
    (kochLammLateShell_far (V := V) x R k)
  have hc : 0 ≤ kochLammFluxTailC V := by
    unfold kochLammFluxTailC kochLammFluxHalfRoot
    exact Real.rpow_nonneg
      (kochLammFluxHalf_nonneg (V := V) one_pos) _
  have hD : 0 ≤ ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2) *
      (kochLammFluxTailC V * (Aₚ : ℝ)) :=
    mul_nonneg
      (mul_nonneg (norm_nonneg w) (Real.exp_pos _).le)
      (mul_nonneg hc (NNReal.coe_nonneg Aₚ))
  have hcardR : (s.card : ℝ) ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact hnorm.trans (mul_le_mul_of_nonneg_right hcardR hD)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
