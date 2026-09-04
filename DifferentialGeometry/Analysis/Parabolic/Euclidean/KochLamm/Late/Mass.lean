import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Kernel
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Time
import Mathlib.MeasureTheory.Integral.Prod

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
omit [FiniteDimensional ℝ V] in
theorem kochLammBasePow_pos {p : ℝ} (hp : 0 < p) :
    0 < basePowMass V p := by
  unfold basePowMass
  exact mul_pos
    (Real.rpow_pos_of_pos (inv_pos.mpr (baseHeatMass_pos (V := V))) _)
    (Real.rpow_pos_of_pos
      (div_pos Real.pi_pos (mul_pos (by positivity) hp)) _)

def kochLammTermPowMass (t : ℝ) (x : V) : ℝ :=
  ∫ z : ℝ × V, ‖kochLammTermKernel t x z‖ ^ kochLammQDual V
    ∂(kochLammTermMeasure (V := V) t)

theorem kochLammTermPowMass_eq {t : ℝ} (ht : 0 < t) (x : V) :
    kochLammTermPowMass t x =
      ((t / 2) ^ (kochLammHeatExp V + 1) / (kochLammHeatExp V + 1)) *
        basePowMass V (kochLammQDual V) := by
  have hp : 0 < kochLammQDual V := (kochLammQ_holder (V := V)).pos
  have hi : Integrable
      (fun z : ℝ × V ↦ ‖kochLammTermKernel t x z‖ ^ kochLammQDual V)
      (kochLammTermMeasure (V := V) t) := by
    have hm := (kochLammTermKernel_memLp (V := V) (t := t) x).integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using hm
  have hi' : Integrable
      (fun z : ℝ × V ↦
        ‖heatKernel (t - z.1) (x - z.2)‖ ^ kochLammQDual V)
      ((volume.restrict (Ioc (t / 2) t)).prod (volume : Measure V)) := by
    simpa only [kochLammTermKernel, kochLammTermMeasure] using hi
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  have hinner :
      (fun s : ℝ ↦
          ∫ y : V, ‖heatKernel (t - s) (x - y)‖ ^ kochLammQDual V) =ᵐ[
        volume.restrict (Ioc (t / 2) t)]
      (fun s : ℝ ↦
          (t - s) ^ kochLammHeatExp V * basePowMass V (kochLammQDual V)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    simp_rw [Real.norm_of_nonneg (heatKernel_nonneg hts _)]
    simpa only [kochLammHeatExp] using
      (heatPow_shift (V := V) hts hp x)
  unfold kochLammTermPowMass kochLammTermMeasure kochLammTermKernel
  rw [integral_prod _ hi']
  rw [integral_congr_ae hinner]
  rw [integral_mul_const]
  rw [kochLammTermTime_set (V := V) ht]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
