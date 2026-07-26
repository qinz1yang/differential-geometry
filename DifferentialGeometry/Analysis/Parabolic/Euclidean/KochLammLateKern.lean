import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLpPower
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammExp
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Terminal-slab Koch--Lamm heat-kernel integrability

The late ordinary-source estimate must use Hölder on space-time, not an
unavailable uniform-in-time spatial source norm.  This file proves the kernel
half of that space-time pairing: on `(t/2,t] × V`, the translated heat kernel
belongs to `L^((n+4)/(n+2))`.
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

/-- Product measure on the terminal half of a Duhamel interval and all of
space. -/
def klTermMeasure (t : ℝ) : Measure (ℝ × V) :=
  (volume.restrict (Ioc (t / 2) t)).prod (volume : Measure V)

/-- Translated heat kernel on the terminal space-time slab. -/
def klTermKernel (t : ℝ) (x : V) (z : ℝ × V) : ℝ :=
  heatKernel (t - z.1) (x - z.2)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The terminal kernel is globally nonnegative, including the null terminal
slice where its heat-time argument is zero. -/
theorem klTermKernel_nonneg (t : ℝ) (x : V) (z : ℝ × V) :
    0 ≤ klTermKernel t x z := by
  unfold klTermKernel heatKernel
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
    (baseHeat_nonneg _)

/-- The terminal translated heat kernel is in the exact Hölder-dual
space-time class needed by the late ordinary-source estimate. -/
theorem klTermKernel_memLp {t : ℝ} (ht : 0 < t) (x : V) :
    MemLp (klTermKernel t x) (ENNReal.ofReal (klQDual V))
      (klTermMeasure (V := V) t) := by
  let p : ℝ := klQDual V
  have hp : 0 < p := (klQ_holder (V := V)).pos
  have hkmeas : Measurable (klTermKernel t x) := by
    unfold klTermKernel heatKernel heatScale baseHeat
    fun_prop
  have hpowmeas : AEStronglyMeasurable
      (fun z : ℝ × V ↦ (klTermKernel t x z) ^ p)
      (klTermMeasure (V := V) t) :=
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
      (fun s : ℝ ↦ (t - s) ^ klHeatExp V * basePowMass V p)
      (volume.restrict (Ioc (t / 2) t)) :=
    (klTimePow_intble (V := V) ht).1.mul_const _
  have houterEq :
      (fun s : ℝ ↦
          ∫ y : V, ‖(heatKernel (t - s) (x - y)) ^ p‖) =ᵐ[
        volume.restrict (Ioc (t / 2) t)]
      (fun s : ℝ ↦ (t - s) ^ klHeatExp V * basePowMass V p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    simp_rw [Real.norm_of_nonneg
      (Real.rpow_nonneg (heatKernel_nonneg hts _) _)]
    simpa [p, klHeatExp] using
      (heatPow_shift (V := V) hts hp x)
  have hpow : Integrable
      (fun z : ℝ × V ↦ (klTermKernel t x z) ^ p)
      (klTermMeasure (V := V) t) := by
    unfold klTermMeasure klTermKernel at hpowmeas ⊢
    apply (integrable_prod_iff hpowmeas).2
    exact ⟨hinner, hbase.congr houterEq.symm⟩
  apply (integrable_norm_rpow_iff hkmeas.aestronglyMeasurable
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
  simpa [ENNReal.toReal_ofReal hp.le, p,
    Real.norm_of_nonneg (klTermKernel_nonneg (V := V) t x _)] using hpow

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
