import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxCover
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateShell

/-!
# Parameterized shell bound for the terminal Koch--Lamm flux

The existing half-open spatial shells are combined with a finite cover whose
cardinality has the canonical polynomial bound.  The terminal flux gains the
split-Gaussian factor `exp (-k^2/8)` on the `k`-th shell.
-/

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
/-- A finite shell cover with the canonical polynomial cardinality bound
inherits the directional Gaussian flux estimate. -/
theorem klFluxShell_norm {T R : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) (w x : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) (k : ℕ) (s : Finset V)
    (hcard : s.card ≤ (5 * (k + 1)) ^ Module.finrank ℝ V)
    (hcover : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * R) ⊆
      ⋃ c ∈ s, Metric.ball c R) :
    ‖klFluxPiece1 R w f x (klLateShell x R k)‖ ≤
      (((5 * (k + 1)) ^ Module.finrank ℝ V : ℕ) : ℝ) *
        (‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2) *
          (klFluxTailC V * (Aₚ : ℝ))) := by
  have hnorm := klFluxCover_norm (V := V) h w x hR
    (Nat.cast_nonneg k) hRT s (klLateShell_mble (V := V) x R k)
    (fun _ hy ↦ hcover (klLateShell_sub (V := V) x R k hy))
    (klLateShell_far (V := V) x R k)
  have hc : 0 ≤ klFluxTailC V := by
    unfold klFluxTailC klFluxHalfRoot
    exact Real.rpow_nonneg
      (klFluxHalf_nonneg (V := V) one_pos) _
  have hD : 0 ≤ ‖w‖ * Real.exp (-(8 : ℝ)⁻¹ * (k : ℝ) ^ 2) *
      (klFluxTailC V * (Aₚ : ℝ)) :=
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
