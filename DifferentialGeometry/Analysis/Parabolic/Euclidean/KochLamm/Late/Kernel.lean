import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.LpPower
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Exponents
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

def kochLammTermMeasure (t : ℝ) : Measure (ℝ × V) :=
  (volume.restrict (Ioc (t / 2) t)).prod (volume : Measure V)

def kochLammTermKernel (t : ℝ) (x : V) (z : ℝ × V) : ℝ :=
  heatKernel (t - z.1) (x - z.2)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem kochLammTermKernel_nonneg (t : ℝ) (x : V) (z : ℝ × V) :
    0 ≤ kochLammTermKernel t x z := by
  unfold kochLammTermKernel heatKernel
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
    (baseHeat_nonneg _)

theorem kochLammTermKernel_memLp {t : ℝ} (x : V) :
    MemLp (kochLammTermKernel t x) (ENNReal.ofReal (kochLammQDual V))
      (kochLammTermMeasure (V := V) t) := by
  let p : ℝ := kochLammQDual V
  have hp : 0 < p := (kochLammQ_holder (V := V)).pos
  have hkmeas : Measurable (kochLammTermKernel t x) := by
    unfold kochLammTermKernel heatKernel heatScale baseHeat
    fun_prop
  have hpowmeas : AEStronglyMeasurable
      (fun z : ℝ × V ↦ (kochLammTermKernel t x z) ^ p)
      (kochLammTermMeasure (V := V) t) :=
    (hkmeas.pow measurable_const).aestronglyMeasurable
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  have hinner : ∀ᵐ s ∂(volume.restrict (Ioc (t / 2) t)),
      Integrable (fun y : V ↦ (heatKernel (t - s) (x - y)) ^ p)
        (volume : Measure V) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    exact (heatKernelPow_mem (V := V) hts hp).comp_sub_left x
  have hbase : Integrable
      (fun s : ℝ ↦ (t - s) ^ kochLammHeatExp V * basePowMass V p)
      (volume.restrict (Ioc (t / 2) t)) :=
    (kochLammTimePow_intble (V := V)).1.mul_const _
  have houterEq :
      (fun s : ℝ ↦
          ∫ y : V, ‖(heatKernel (t - s) (x - y)) ^ p‖) =ᵐ[
        volume.restrict (Ioc (t / 2) t)]
      (fun s : ℝ ↦ (t - s) ^ kochLammHeatExp V * basePowMass V p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    simp_rw [Real.norm_of_nonneg
      (Real.rpow_nonneg (heatKernel_nonneg hts _) _)]
    simpa [p, kochLammHeatExp] using
      (heatPow_shift (V := V) hts hp x)
  have hpow : Integrable
      (fun z : ℝ × V ↦ (kochLammTermKernel t x z) ^ p)
      (kochLammTermMeasure (V := V) t) := by
    unfold kochLammTermMeasure kochLammTermKernel at hpowmeas ⊢
    apply (integrable_prod_iff hpowmeas).2
    exact ⟨hinner, hbase.congr houterEq.symm⟩
  apply (integrable_norm_rpow_iff hkmeas.aestronglyMeasurable
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
  simpa [ENNReal.toReal_ofReal hp.le, p,
    Real.norm_of_nonneg (kochLammTermKernel_nonneg (V := V) t x _)] using hpow

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
