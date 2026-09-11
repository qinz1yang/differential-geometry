import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.FirstDerivative.LpPower
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Flux.Exponents
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLamm.Late.Kernel
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

def kochLammFluxKernel (t : ℝ) (w x : V) (z : ℝ × V) : ℝ :=
  heatD1 (t - z.1) w (x - z.2)

def kochLammFluxMajor (t : ℝ) (x : V) (z : ℝ × V) : ℝ :=
  heatD1Maj (t - z.1) (x - z.2)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem kochLammFluxMajor_nonneg (t : ℝ) (x : V) (z : ℝ × V) :
    0 ≤ kochLammFluxMajor t x z := by
  unfold kochLammFluxMajor heatD1Maj
  exact mul_nonneg
    (mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
      (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (baseD1Maj_nonneg _)

theorem kochLammFluxMajor_memLp {t : ℝ} (x : V) :
    MemLp (kochLammFluxMajor t x) (ENNReal.ofReal (kochLammPDual V))
      (kochLammTermMeasure (V := V) t) := by
  let p : ℝ := kochLammPDual V
  have hp : 0 < p := (kochLammPDual_holder (V := V)).pos
  have hmmeas : Measurable (kochLammFluxMajor t x) := by
    unfold kochLammFluxMajor heatD1Maj heatScale baseD1Maj baseHeat baseHeatMass
    fun_prop
  have hpowmeas : AEStronglyMeasurable
      (fun z : ℝ × V ↦ (kochLammFluxMajor t x z) ^ p)
      (kochLammTermMeasure (V := V) t) :=
    (hmmeas.pow measurable_const).aestronglyMeasurable
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  have hinner : ∀ᵐ s ∂(volume.restrict (Ioc (t / 2) t)),
      Integrable (fun y : V ↦ (heatD1Maj (t - s) (x - y)) ^ p)
        (volume : Measure V) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    have hscaled : Integrable (fun y : V ↦ (heatD1Maj (t - s) y) ^ p) := by
      simp_rw [heatD1Maj_pow (V := V) hts]
      exact ((baseD1Maj_rpow (V := V) (kochLammPDual_one (V := V))
        (kochLammPDual_two (V := V))).comp_smul
          (inv_ne_zero (heatScale_pos hts).ne')).const_mul _
    exact hscaled.comp_sub_left x
  have hbase : Integrable
      (fun s : ℝ ↦ (t - s) ^ kochLammD1Exp V * baseD1PowMass V p)
      (volume.restrict (Ioc (t / 2) t)) :=
    (kochLammD1Time_intble (V := V)).1.mul_const _
  have houterEq :
      (fun s : ℝ ↦
          ∫ y : V, ‖(heatD1Maj (t - s) (x - y)) ^ p‖) =ᵐ[
        volume.restrict (Ioc (t / 2) t)]
      (fun s : ℝ ↦ (t - s) ^ kochLammD1Exp V * baseD1PowMass V p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    simp_rw [Real.norm_of_nonneg
      (Real.rpow_nonneg (heatD1Maj_nonneg hts _) _)]
    simpa [p, kochLammD1Exp] using
      (heatD1Pow_shift (V := V) (p := p) hts x)
  have hpow : Integrable
      (fun z : ℝ × V ↦ (kochLammFluxMajor t x z) ^ p)
      (kochLammTermMeasure (V := V) t) := by
    unfold kochLammTermMeasure kochLammFluxMajor at hpowmeas ⊢
    apply (integrable_prod_iff hpowmeas).2
    exact ⟨hinner, hbase.congr houterEq.symm⟩
  apply (integrable_norm_rpow_iff hmmeas.aestronglyMeasurable
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
  simpa [ENNReal.toReal_ofReal hp.le, p,
    Real.norm_of_nonneg (kochLammFluxMajor_nonneg (V := V) t x _)] using hpow

omit [Nontrivial V] in
theorem kochLammFluxKernel_ae {t : ℝ} (w x : V) :
    ∀ᵐ z ∂(kochLammTermMeasure (V := V) t),
      ‖kochLammFluxKernel t w x z‖ ≤ ‖w‖ * kochLammFluxMajor t x z := by
  have hkmeas0 : Measurable (kochLammFluxKernel t w x) := by
    unfold kochLammFluxKernel heatD1 heatScale baseD1 baseHeat baseHeatMass
    fun_prop
  have hmmeas0 : Measurable (kochLammFluxMajor t x) := by
    unfold kochLammFluxMajor heatD1Maj heatScale baseD1Maj baseHeat baseHeatMass
    fun_prop
  have htime : ∀ᵐ s ∂(volume.restrict (Ioc (t / 2) t)), s ≠ t := by
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
      simp [ae_iff, measure_singleton]
    exact ae_restrict_of_ae hne
  unfold kochLammTermMeasure
  apply (Measure.ae_prod_iff_ae_ae (by
    exact measurableSet_le hkmeas0.norm
      (measurable_const.mul hmmeas0))).2
  filter_upwards [ae_restrict_mem measurableSet_Ioc, htime] with s hs hst
  have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  filter_upwards with y
  simpa only [kochLammFluxKernel, kochLammFluxMajor] using
    (heatD1_bound (V := V) hts w (x - y))

theorem kochLammFluxKernel_memLp {t : ℝ} (w x : V) :
    MemLp (kochLammFluxKernel t w x) (ENNReal.ofReal (kochLammPDual V))
      (kochLammTermMeasure (V := V) t) := by
  have hkmeas : AEStronglyMeasurable (kochLammFluxKernel t w x)
      (kochLammTermMeasure (V := V) t) := by
    apply Measurable.aestronglyMeasurable
    unfold kochLammFluxKernel heatD1 heatScale baseD1 baseHeat baseHeatMass
    fun_prop
  have hbound : ∀ᵐ z ∂(kochLammTermMeasure (V := V) t),
      ‖kochLammFluxKernel t w x z‖ ≤ ‖‖w‖ * kochLammFluxMajor t x z‖ :=
    (kochLammFluxKernel_ae (V := V) w x).mono fun z hz ↦ by
      simpa only [Real.norm_of_nonneg (norm_nonneg w),
        Real.norm_of_nonneg (kochLammFluxMajor_nonneg (V := V) t x z), norm_mul]
        using hz
  exact MemLp.mono
    ((kochLammFluxMajor_memLp (V := V) (t := t) x).const_mul ‖w‖)
    hkmeas hbound

def kochLammFluxPowMass (t : ℝ) (x : V) : ℝ :=
  ∫ z : ℝ × V, ‖kochLammFluxMajor t x z‖ ^ kochLammPDual V
    ∂(kochLammTermMeasure (V := V) t)

theorem kochLammFluxPowMass_eq {t : ℝ} (ht : 0 < t) (x : V) :
    kochLammFluxPowMass t x =
      ((t / 2) ^ (kochLammD1Exp V + 1) / (kochLammD1Exp V + 1)) *
        baseD1PowMass V (kochLammPDual V) := by
  have hp : 0 < kochLammPDual V := (kochLammPDual_holder (V := V)).pos
  have hi : Integrable
      (fun z : ℝ × V ↦ ‖kochLammFluxMajor t x z‖ ^ kochLammPDual V)
      (kochLammTermMeasure (V := V) t) := by
    have hm := (kochLammFluxMajor_memLp (V := V) (t := t) x).integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using hm
  have hi' : Integrable
      (fun z : ℝ × V ↦
        ‖heatD1Maj (t - z.1) (x - z.2)‖ ^ kochLammPDual V)
      ((volume.restrict (Ioc (t / 2) t)).prod (volume : Measure V)) := by
    simpa only [kochLammFluxMajor, kochLammTermMeasure] using hi
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  have hinner :
      (fun s : ℝ ↦
          ∫ y : V, ‖heatD1Maj (t - s) (x - y)‖ ^ kochLammPDual V) =ᵐ[
        volume.restrict (Ioc (t / 2) t)]
      (fun s : ℝ ↦
          (t - s) ^ kochLammD1Exp V * baseD1PowMass V (kochLammPDual V)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    simp_rw [Real.norm_of_nonneg (heatD1Maj_nonneg hts _)]
    simpa only [kochLammD1Exp] using
      (heatD1Pow_shift (V := V) (p := kochLammPDual V) hts x)
  unfold kochLammFluxPowMass kochLammTermMeasure kochLammFluxMajor
  rw [integral_prod _ hi']
  rw [integral_congr_ae hinner]
  rw [integral_mul_const]
  rw [kochLammD1Time_set (V := V) ht]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
