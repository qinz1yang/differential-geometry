import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateKern
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateTime
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact terminal heat-kernel power mass

The terminal ordinary-source estimate needs the full space-time
`L^((n+4)/(n+2))` norm of the heat kernel.  This file evaluates its power
integral exactly by Fubini, the translated spatial heat-kernel mass, and the
one-dimensional terminal-time formula.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The exact positive-power mass of the normalized time-one heat kernel is
strictly positive. -/
theorem klBasePow_pos {p : ℝ} (hp : 0 < p) :
    0 < basePowMass V p := by
  unfold basePowMass
  exact mul_pos
    (Real.rpow_pos_of_pos (inv_pos.mpr (baseHeatMass_pos (V := V))) _)
    (Real.rpow_pos_of_pos
      (div_pos Real.pi_pos (mul_pos (by positivity) hp)) _)

/-- The real `klQDual`-power mass of the translated heat kernel on the full
terminal slab. -/
def klTermPowMass (t : ℝ) (x : V) : ℝ :=
  ∫ z : ℝ × V, ‖klTermKernel t x z‖ ^ klQDual V
    ∂(klTermMeasure (V := V) t)

/-- Exact Fubini evaluation of the terminal heat-kernel power mass. -/
theorem klTermPowMass_eq {t : ℝ} (ht : 0 < t) (x : V) :
    klTermPowMass t x =
      ((t / 2) ^ (klHeatExp V + 1) / (klHeatExp V + 1)) *
        basePowMass V (klQDual V) := by
  have hp : 0 < klQDual V := (klQ_holder (V := V)).pos
  have hi : Integrable
      (fun z : ℝ × V ↦ ‖klTermKernel t x z‖ ^ klQDual V)
      (klTermMeasure (V := V) t) := by
    have hm := (klTermKernel_memLp (V := V) ht x).integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using hm
  have hi' : Integrable
      (fun z : ℝ × V ↦
        ‖heatKernel (t - z.1) (x - z.2)‖ ^ klQDual V)
      ((volume.restrict (Ioc (t / 2) t)).prod (volume : Measure V)) := by
    simpa only [klTermKernel, klTermMeasure] using hi
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  have hinner :
      (fun s : ℝ ↦
          ∫ y : V, ‖heatKernel (t - s) (x - y)‖ ^ klQDual V) =ᵐ[
        volume.restrict (Ioc (t / 2) t)]
      (fun s : ℝ ↦
          (t - s) ^ klHeatExp V * basePowMass V (klQDual V)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    simp_rw [Real.norm_of_nonneg (heatKernel_nonneg hts _)]
    simpa only [klHeatExp] using
      (heatPow_shift (V := V) hts hp x)
  unfold klTermPowMass klTermMeasure klTermKernel
  rw [integral_prod _ hi']
  rw [integral_congr_ae hinner]
  rw [integral_mul_const]
  rw [klTermTime_set (V := V) ht]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
