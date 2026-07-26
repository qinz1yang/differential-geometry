import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelDuhamel
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelSup

/-!
# Lower spatial jets of the Euclidean heat potential

The second derivative of a heat potential needs spatial cancellation and is
handled in `HeatKernelDuhamel`.  The value and first derivative are genuinely
lower order: a uniformly bounded forcing path gives respectively a `t` and a
`sqrt t` gain.  This file proves those two estimates for a general
time-dependent bounded forcing path.

These are the dimension-generic small-time factors used by the first- and
zero-order arm of a frozen-coefficient parametrix.  No spatial derivative of
the forcing and no Sobolev input is assumed.
-/

noncomputable section

open MeasureTheory Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section ValuePotential

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Constant time majorant for the value heat potential. -/
def d0DuhMajor (K : ℝ≥0) (_t _s : ℝ) : ℝ := K

/-- The value-potential majorant is interval integrable. -/
theorem d0DuhMajor_intble (t : ℝ) (K : ℝ≥0) :
    IntervalIntegrable (d0DuhMajor K t) volume 0 t := by
  simpa only [d0DuhMajor] using
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (K : ℝ)) volume 0 t)

/-- Exact integral of the value-potential majorant. -/
theorem d0DuhMajor_int (t : ℝ) (K : ℝ≥0) :
    ∫ s : ℝ in 0..t, d0DuhMajor K t s = t * (K : ℝ) := by
  simp only [d0DuhMajor, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul]

/-- Time Duhamel integral of the heat evolution of a bounded forcing path. -/
def heatDuh (t : ℝ) (f : ℝ → BoundedContinuousFunction V F) (x : V) : F :=
  ∫ s : ℝ in 0..t, heatSup (t - s) (f s) x

/-- A strongly measurable, uniformly bounded forcing path has an integrable
value heat-potential integrand. -/
theorem heatDuh_int {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K) (x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatSup (t - s) (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    IntervalIntegrable
      (fun s : ℝ => heatSup (t - s) (f s) x) volume 0 t := by
  apply (d0DuhMajor_intble t K).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := Set.uIoc (0 : ℝ) t) hne] with s hs hst
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  calc
    ‖heatSup (t - s) (f s) x‖ ≤ ‖f s‖ :=
      heatSup_contract (sub_pos.mpr hstlt) (f s) x
    _ ≤ K := hf s ⟨hs.1.le, hs.2⟩
    _ = d0DuhMajor K t s := by rfl

/-- The value heat potential gains one full power of the time horizon. -/
theorem heatDuh_norm {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K) (x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatSup (t - s) (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    ‖heatDuh t f x‖ ≤ t * (K : ℝ) := by
  have hint := heatDuh_int ht f hf x hmeas
  unfold heatDuh
  calc
    ‖∫ s : ℝ in 0..t, heatSup (t - s) (f s) x‖ ≤
        ∫ s : ℝ in 0..t, ‖heatSup (t - s) (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s : ℝ in 0..t, d0DuhMajor K t s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm
        (d0DuhMajor_intble t K)
      intro s hs
      calc
        ‖heatSup (t - s) (f s) x‖ ≤ ‖f s‖ :=
          heatSup_contract (sub_pos.mpr hs.2) (f s) x
        _ ≤ K := hf s ⟨hs.1.le, hs.2.le⟩
        _ = d0DuhMajor K t s := by rfl
    _ = t * (K : ℝ) := d0DuhMajor_int t K

/-- On a horizon at most one, the value estimate may be absorbed into the
common `sqrt t` lower-jet factor. -/
theorem heatDuh_sqrt {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K) (x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatSup (t - s) (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    ‖heatDuh t f x‖ ≤ Real.sqrt t * (K : ℝ) := by
  have htsqrt : t ≤ Real.sqrt t := by
    have hsqrt_le : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
    nlinarith [Real.sq_sqrt ht.le, Real.sqrt_nonneg t]
  exact (heatDuh_norm ht f hf x hmeas).trans
    (mul_le_mul_of_nonneg_right htsqrt NNReal.coe_nonneg)

end ValuePotential

section GradientPotential

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Constant multiplying the reflected `t^(-1/2)` gradient majorant. -/
def d1DuhConst (v : V) (K : ℝ≥0) : ℝ :=
  ‖v‖ * (K : ℝ) * heatC1 V

/-- Scalar time majorant for the first spatial derivative of a heat
potential. -/
def d1DuhMajor (v : V) (K : ℝ≥0) (t s : ℝ) : ℝ :=
  d1DuhConst v K * heatScale12 (t - s)

/-- The gradient-potential majorant is interval integrable. -/
theorem d1DuhMajor_intble {t : ℝ} (ht : 0 < t) (v : V) (K : ℝ≥0) :
    IntervalIntegrable (d1DuhMajor v K t) volume 0 t := by
  exact (scale12_intble ht).const_mul (d1DuhConst v K)

/-- Exact integral of the gradient-potential majorant. -/
theorem d1DuhMajor_int {t : ℝ} (ht : 0 < t) (v : V) (K : ℝ≥0) :
    ∫ s : ℝ in 0..t, d1DuhMajor v K t s =
      d1DuhConst v K * (2 * t ^ (1 / 2 : ℝ)) := by
  unfold d1DuhMajor
  rw [intervalIntegral.integral_const_mul, timeScale12_int ht]

/-- Time Duhamel integral of the first spatial heat derivative. -/
def heatD1Duh (t : ℝ) (v : V)
    (f : ℝ → BoundedContinuousFunction V F) (x : V) : F :=
  ∫ s : ℝ in 0..t, heatD1Sup (t - s) v (f s) x

/-- A strongly measurable, uniformly bounded forcing path has an integrable
first-derivative heat-potential integrand. -/
theorem heatD1Duh_int {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K)
    (v x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatD1Sup (t - s) v (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    IntervalIntegrable
      (fun s : ℝ => heatD1Sup (t - s) v (f s) x) volume 0 t := by
  apply (d1DuhMajor_intble ht v K).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := Set.uIoc (0 : ℝ) t) hne] with s hs hst
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  have hpos : 0 < t - s := sub_pos.mpr hstlt
  have hcoef : 0 ≤ ‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V := by
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (heatScale_pos hpos).le))
      (heatC1_nonneg (V := V))
  calc
    ‖heatD1Sup (t - s) v (f s) x‖ ≤
        (‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V) * ‖f s‖ :=
      heatD1Sup_norm hpos v (f s) x
    _ ≤ (‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V) * (K : ℝ) :=
      mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2⟩) hcoef
    _ = d1DuhMajor v K t s := by
      rw [← heatScale12_eq hpos]
      unfold d1DuhMajor d1DuhConst
      ring

/-- The first spatial derivative of the heat potential gains the explicit
factor `2 * sqrt t`. -/
theorem heatD1Duh_norm {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K)
    (v x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatD1Sup (t - s) v (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    ‖heatD1Duh t v f x‖ ≤
      2 * d1DuhConst v K * Real.sqrt t := by
  have hint := heatD1Duh_int ht f hf v x hmeas
  unfold heatD1Duh
  calc
    ‖∫ s : ℝ in 0..t, heatD1Sup (t - s) v (f s) x‖ ≤
        ∫ s : ℝ in 0..t, ‖heatD1Sup (t - s) v (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s : ℝ in 0..t, d1DuhMajor v K t s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm
        (d1DuhMajor_intble ht v K)
      intro s hs
      have hpos : 0 < t - s := sub_pos.mpr hs.2
      have hcoef : 0 ≤ ‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V := by
        exact mul_nonneg
          (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (heatScale_pos hpos).le))
          (heatC1_nonneg (V := V))
      calc
        ‖heatD1Sup (t - s) v (f s) x‖ ≤
            (‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V) * ‖f s‖ :=
          heatD1Sup_norm hpos v (f s) x
        _ ≤ (‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V) *
            (K : ℝ) :=
          mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2.le⟩) hcoef
        _ = d1DuhMajor v K t s := by
          rw [← heatScale12_eq hpos]
          unfold d1DuhMajor d1DuhConst
          ring
    _ = d1DuhConst v K * (2 * t ^ (1 / 2 : ℝ)) :=
      d1DuhMajor_int ht v K
    _ = 2 * d1DuhConst v K * Real.sqrt t := by
      rw [Real.sqrt_eq_rpow]
      ring

end GradientPotential

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

