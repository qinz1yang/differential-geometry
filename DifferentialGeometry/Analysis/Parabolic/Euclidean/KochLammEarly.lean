import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatEarlyGlobal
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammSpaces

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [MeasurableSpace V]
  [BorelSpace V]
  [Nontrivial V] in
theorem klL1Scale_inv {R : ℝ} (hR : 0 < R) :
    (klL1Scale (V := V) R)⁻¹ =
      ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
  simp [klL1Scale, klL1ScaleR, klDim, Real.rpow_neg hR.le,
    Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (pow_pos hR _)]

omit [NormedSpace ℝ F]
  [CompleteSpace F]
  [Nontrivial V] in
theorem kl0_to_srcCarl {T : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) :
    SrcCarl T (A₁ : ℝ≥0∞) f := by
  refine ⟨?_, ?_⟩
  · simpa [klVolume, stVolume] using h.ae
  · intro x R hR hRT
    have hb := h.local_l1 x R hR hRT
    have hs0 : klL1Scale (V := V) R ≠ 0 := by
      exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hR (-klDim V))).ne'
    have hsT : klL1Scale (V := V) R ≠ ∞ := ENNReal.ofReal_ne_top
    have hi := (ENNReal.mul_le_iff_le_inv hs0 hsT).mp hb
    rw [klL1Scale_inv (V := V) hR] at hi
    simpa [srcMass, paraCyl, klCyl, stVolume, klVolume, mul_comm,
      eLpNorm_one_eq_lintegral_enorm, ofReal_norm_eq_enorm] using hi

omit [CompleteSpace F] in
theorem kl0_early_norm {T t : ℝ} {A₁ A_q : ℝ≥0}
    (ht : 0 < t) (htT : t ≤ T) (f : ℝ × V → F) (x : V)
    (h : KLSource0 T A₁ A_q f) :
    ‖heatEarly0 t f x‖ₑ ≤ earlyHeatC V * (A₁ : ℝ≥0∞) :=
  heatEarly0_norm ht htT f x (kl0_to_srcCarl h)

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
