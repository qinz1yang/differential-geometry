import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatD1LpPower
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammFluxExp
import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLateKern
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Terminal-slab Koch--Lamm first-derivative kernel

The late divergence-source estimate pairs an `L^(n+4)` source with the first
spatial derivative of the heat kernel on the terminal half-cylinder.  This
file proves the corresponding full-space terminal-slab `L^p'` membership and
evaluates the exact power mass of the radial derivative majorant.
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

/-- A directional first spatial derivative of the translated heat kernel on
the terminal space-time slab. -/
def klFluxKernel (t : ℝ) (w x : V) (z : ℝ × V) : ℝ :=
  heatD1 (t - z.1) w (x - z.2)

/-- Radial majorant for the terminal first-derivative kernel. -/
def klFluxMajor (t : ℝ) (x : V) (z : ℝ × V) : ℝ :=
  heatD1Maj (t - z.1) (x - z.2)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The radial terminal first-derivative majorant is nonnegative even on the
null terminal slice. -/
theorem klFluxMajor_nonneg (t : ℝ) (x : V) (z : ℝ × V) :
    0 ≤ klFluxMajor t x z := by
  unfold klFluxMajor heatD1Maj
  exact mul_nonneg
    (mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _))
      (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (baseD1Maj_nonneg _)

/-- The radial first-derivative majorant is in the exact Hölder-dual
space-time class on the full terminal slab. -/
theorem klFluxMajor_memLp {t : ℝ} (ht : 0 < t) (x : V) :
    MemLp (klFluxMajor t x) (ENNReal.ofReal (klPDual V))
      (klTermMeasure (V := V) t) := by
  let p : ℝ := klPDual V
  have hp : 0 < p := (klP_holder (V := V)).pos
  have hmmeas : Measurable (klFluxMajor t x) := by
    unfold klFluxMajor heatD1Maj heatScale baseD1Maj baseHeat baseHeatMass
    fun_prop
  have hpowmeas : AEStronglyMeasurable
      (fun z : ℝ × V ↦ (klFluxMajor t x z) ^ p)
      (klTermMeasure (V := V) t) :=
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
      exact ((baseD1Maj_rpow (V := V) (klPDual_one (V := V))
        (klPDual_two (V := V))).comp_smul
          (inv_ne_zero (heatScale_pos hts).ne')).const_mul _
    exact hscaled.comp_sub_left x
  have hbase : Integrable
      (fun s : ℝ ↦ (t - s) ^ klD1Exp V * baseD1PowMass V p)
      (volume.restrict (Ioc (t / 2) t)) :=
    (klD1Time_intble (V := V) ht).1.mul_const _
  have houterEq :
      (fun s : ℝ ↦
          ∫ y : V, ‖(heatD1Maj (t - s) (x - y)) ^ p‖) =ᵐ[
        volume.restrict (Ioc (t / 2) t)]
      (fun s : ℝ ↦ (t - s) ^ klD1Exp V * baseD1PowMass V p) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    simp_rw [Real.norm_of_nonneg
      (Real.rpow_nonneg (heatD1Maj_nonneg hts _) _)]
    simpa [p, klD1Exp] using
      (heatD1Pow_shift (V := V) (p := p) hts x)
  have hpow : Integrable
      (fun z : ℝ × V ↦ (klFluxMajor t x z) ^ p)
      (klTermMeasure (V := V) t) := by
    unfold klTermMeasure klFluxMajor at hpowmeas ⊢
    apply (integrable_prod_iff hpowmeas).2
    exact ⟨hinner, hbase.congr houterEq.symm⟩
  apply (integrable_norm_rpow_iff hmmeas.aestronglyMeasurable
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
  simpa [ENNReal.toReal_ofReal hp.le, p,
    Real.norm_of_nonneg (klFluxMajor_nonneg (V := V) t x _)] using hpow

omit [Nontrivial V] in
/-- On the terminal slab, every directional first-derivative heat kernel is
almost everywhere bounded by the radial majorant times the direction norm. -/
theorem klFluxKernel_ae {t : ℝ} (_ht : 0 < t) (w x : V) :
    ∀ᵐ z ∂(klTermMeasure (V := V) t),
      ‖klFluxKernel t w x z‖ ≤ ‖w‖ * klFluxMajor t x z := by
  have hkmeas0 : Measurable (klFluxKernel t w x) := by
    unfold klFluxKernel heatD1 heatScale baseD1 baseHeat baseHeatMass
    fun_prop
  have hmmeas0 : Measurable (klFluxMajor t x) := by
    unfold klFluxMajor heatD1Maj heatScale baseD1Maj baseHeat baseHeatMass
    fun_prop
  have htime : ∀ᵐ s ∂(volume.restrict (Ioc (t / 2) t)), s ≠ t := by
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
      simp [ae_iff, measure_singleton]
    exact ae_restrict_of_ae hne
  unfold klTermMeasure
  apply (Measure.ae_prod_iff_ae_ae (by
    exact measurableSet_le hkmeas0.norm
      (measurable_const.mul hmmeas0))).2
  filter_upwards [ae_restrict_mem measurableSet_Ioc, htime] with s hs hst
  have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  filter_upwards with y
  simpa only [klFluxKernel, klFluxMajor] using
    (heatD1_bound (V := V) hts w (x - y))

/-- Every directional terminal first-derivative kernel belongs to the same
Hölder-dual space-time class. -/
theorem klFluxKernel_memLp {t : ℝ} (ht : 0 < t) (w x : V) :
    MemLp (klFluxKernel t w x) (ENNReal.ofReal (klPDual V))
      (klTermMeasure (V := V) t) := by
  have hkmeas : AEStronglyMeasurable (klFluxKernel t w x)
      (klTermMeasure (V := V) t) := by
    apply Measurable.aestronglyMeasurable
    unfold klFluxKernel heatD1 heatScale baseD1 baseHeat baseHeatMass
    fun_prop
  have hbound : ∀ᵐ z ∂(klTermMeasure (V := V) t),
      ‖klFluxKernel t w x z‖ ≤ ‖‖w‖ * klFluxMajor t x z‖ :=
    (klFluxKernel_ae (V := V) ht w x).mono fun z hz ↦ by
      simpa only [Real.norm_of_nonneg (norm_nonneg w),
        Real.norm_of_nonneg (klFluxMajor_nonneg (V := V) t x z), norm_mul]
        using hz
  exact MemLp.mono
    ((klFluxMajor_memLp (V := V) ht x).const_mul ‖w‖)
    hkmeas hbound

/-- Real `klPDual`-power mass of the radial first-derivative majorant on the
full terminal slab. -/
def klFluxPowMass (t : ℝ) (x : V) : ℝ :=
  ∫ z : ℝ × V, ‖klFluxMajor t x z‖ ^ klPDual V
    ∂(klTermMeasure (V := V) t)

/-- Exact Fubini evaluation of the terminal first-derivative majorant power
mass. -/
theorem klFluxPowMass_eq {t : ℝ} (ht : 0 < t) (x : V) :
    klFluxPowMass t x =
      ((t / 2) ^ (klD1Exp V + 1) / (klD1Exp V + 1)) *
        baseD1PowMass V (klPDual V) := by
  have hp : 0 < klPDual V := (klP_holder (V := V)).pos
  have hi : Integrable
      (fun z : ℝ × V ↦ ‖klFluxMajor t x z‖ ^ klPDual V)
      (klTermMeasure (V := V) t) := by
    have hm := (klFluxMajor_memLp (V := V) ht x).integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hp.le] using hm
  have hi' : Integrable
      (fun z : ℝ × V ↦
        ‖heatD1Maj (t - z.1) (x - z.2)‖ ^ klPDual V)
      ((volume.restrict (Ioc (t / 2) t)).prod (volume : Measure V)) := by
    simpa only [klFluxMajor, klTermMeasure] using hi
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  have hinner :
      (fun s : ℝ ↦
          ∫ y : V, ‖heatD1Maj (t - s) (x - y)‖ ^ klPDual V) =ᵐ[
        volume.restrict (Ioc (t / 2) t)]
      (fun s : ℝ ↦
          (t - s) ^ klD1Exp V * baseD1PowMass V (klPDual V)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with s hs hst
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    simp_rw [Real.norm_of_nonneg (heatD1Maj_nonneg hts _)]
    simpa only [klD1Exp] using
      (heatD1Pow_shift (V := V) (p := klPDual V) hts x)
  unfold klFluxPowMass klTermMeasure klFluxMajor
  rw [integral_prod _ hi']
  rw [integral_congr_ae hinner]
  rw [integral_mul_const]
  rw [klD1Time_set (V := V) ht]

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
