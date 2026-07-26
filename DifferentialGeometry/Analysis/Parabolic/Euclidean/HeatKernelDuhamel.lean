import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelCancel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Time-integrated second-heat-derivative cancellation

The spatial cancellation estimate for `D^2 H_t` has singular factor
`t^(-3/4)`.  This file performs the remaining time integration.  Its exact
primitive is `4 * t^(1/4)`, so a Duhamel second derivative gains a small
`t^(1/4)` factor from a time-uniform spatial `C^{0,1/2}` bound.

The Banach-valued integrability theorem asks only for strong measurability in
time.  No time derivative, slice Sobolev norm, or uniform continuity on the
noncompact Euclidean chart is hidden in the interface.
-/

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section TimeKernel

/-- The first-heat-derivative time singularity, written as a real power. -/
def heatScale12 (t : ℝ) : ℝ :=
  t ^ (-(1 : ℝ) / 2)

/-- At positive time the power-form singularity is the inverse heat scale. -/
theorem heatScale12_eq {t : ℝ} (ht : 0 < t) :
    heatScale12 t = (heatScale t)⁻¹ := by
  unfold heatScale12 heatScale
  rw [Real.sqrt_eq_rpow]
  convert Real.rpow_neg ht.le (1 / 2 : ℝ) using 1
  ring_nf

/-- The `t^(-1/2)` first-derivative heat singularity is interval integrable
after reflection about the terminal time. -/
theorem scale12_intble {t : ℝ} (_ht : 0 < t) :
    IntervalIntegrable (fun s : ℝ => heatScale12 (t - s)) volume 0 t := by
  have hpow : IntervalIntegrable (fun u : ℝ => u ^ (-(1 : ℝ) / 2)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have href := hpow.symm.comp_sub_left t
  simpa only [heatScale12, sub_self, sub_zero] using href

/-- Exact primitive of the reflected `t^(-1/2)` singularity. -/
theorem timeScale12_int {t : ℝ} (_ht : 0 < t) :
    ∫ s : ℝ in 0..t, heatScale12 (t - s) =
      2 * t ^ (1 / 2 : ℝ) := by
  unfold heatScale12
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => u ^ (-(1 : ℝ) / 2)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num))]
  have hexp : -(1 : ℝ) / 2 + 1 = 1 / 2 := by ring
  rw [hexp, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  ring

/-- The `t^(-3/4)` heat-cancellation singularity is interval integrable after
reflection about the terminal time. -/
theorem scale34_intble {t : ℝ} (_ht : 0 < t) :
    IntervalIntegrable (fun s : ℝ => heatScale34 (t - s)) volume 0 t := by
  have hpow : IntervalIntegrable (fun u : ℝ => u ^ (-(3 : ℝ) / 4)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have href := hpow.symm.comp_sub_left t
  simpa only [heatScale34, sub_self, sub_zero] using href

/-- Exact primitive of the reflected `t^(-3/4)` singularity. -/
theorem timeScale34_int {t : ℝ} (_ht : 0 < t) :
    ∫ s : ℝ in 0..t, heatScale34 (t - s) =
      4 * t ^ (1 / 4 : ℝ) := by
  unfold heatScale34
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => u ^ (-(3 : ℝ) / 4)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num))]
  have hexp : -(3 : ℝ) / 4 + 1 = 1 / 4 := by ring
  rw [hexp, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  ring

end TimeKernel

section Duhamel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Constant multiplying the reflected `t^(-3/4)` Duhamel majorant. -/
def d2DuhConst (v w : V) (K : ℝ≥0) : ℝ :=
  ‖v‖ * ‖w‖ * (K : ℝ) * heatC2Half V

/-- Scalar time majorant for the cancelled second-derivative Duhamel
integrand. -/
def d2DuhMajor (v w : V) (K : ℝ≥0) (t s : ℝ) : ℝ :=
  d2DuhConst v w K * heatScale34 (t - s)

omit [Nontrivial V] in
/-- The scalar Duhamel majorant is interval integrable. -/
theorem d2DuhMajor_intble {t : ℝ} (ht : 0 < t) (v w : V) (K : ℝ≥0) :
    IntervalIntegrable (d2DuhMajor v w K t) volume 0 t := by
  exact (scale34_intble ht).const_mul (d2DuhConst v w K)

omit [Nontrivial V] in
/-- Exact integral of the scalar Duhamel majorant. -/
theorem d2DuhMajor_int {t : ℝ} (ht : 0 < t) (v w : V) (K : ℝ≥0) :
    ∫ s : ℝ in 0..t, d2DuhMajor v w K t s =
      d2DuhConst v w K * (4 * t ^ (1 / 4 : ℝ)) := by
  unfold d2DuhMajor
  rw [intervalIntegral.integral_const_mul, timeScale34_int ht]

/-- Time Duhamel integral of the raw second heat derivative.  Spatial
cancellation is inserted by `heatD2Conv_eq_cancel` in the estimates below. -/
def heatD2Duh (t : ℝ) (v w : V) (f : ℝ → V → F) (x : V) : F :=
  ∫ s : ℝ in 0..t, heatD2Conv (t - s) v w (f s) x

/-- A strongly measurable time path with one uniform spatial
`1/2`-Holder constant has an interval-integrable cancelled `D^2` Duhamel
integrand. -/
theorem heatD2Duh_int {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → V → F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HolderWith K (1 / 2 : ℝ≥0) (f s))
    (v w x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatD2Conv (t - s) v w (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    IntervalIntegrable
      (fun s : ℝ => heatD2Conv (t - s) v w (f s) x) volume 0 t := by
  apply (d2DuhMajor_intble ht v w K).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := Set.uIoc (0 : ℝ) t) hne] with s hs hst
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  rw [heatD2Conv_eq_cancel (sub_pos.mpr hstlt) (hf s ⟨hs.1.le, hs.2⟩) v w x]
  refine (heatD2Cancel_norm (sub_pos.mpr hstlt)
    (hf s ⟨hs.1.le, hs.2⟩) v w x).trans_eq ?_
  unfold d2DuhMajor d2DuhConst
  ring

/-- Time-integrated Schauder cancellation estimate.  The contraction gain is
the explicit factor `4 * t^(1/4)`. -/
theorem heatD2Duh_norm {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → V → F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HolderWith K (1 / 2 : ℝ≥0) (f s))
    (v w x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatD2Conv (t - s) v w (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    ‖heatD2Duh t v w f x‖ ≤
      d2DuhConst v w K * (4 * t ^ (1 / 4 : ℝ)) := by
  have hint := heatD2Duh_int ht f hf v w x hmeas
  unfold heatD2Duh
  calc
    ‖∫ s : ℝ in 0..t, heatD2Conv (t - s) v w (f s) x‖
        ≤ ∫ s : ℝ in 0..t, ‖heatD2Conv (t - s) v w (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s : ℝ in 0..t, d2DuhMajor v w K t s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm
        (d2DuhMajor_intble ht v w K)
      intro s hs
      rw [heatD2Conv_eq_cancel (sub_pos.mpr hs.2)
        (hf s ⟨hs.1.le, hs.2.le⟩) v w x]
      refine (heatD2Cancel_norm (sub_pos.mpr hs.2)
        (hf s ⟨hs.1.le, hs.2.le⟩) v w x).trans_eq ?_
      unfold d2DuhMajor d2DuhConst
      ring
    _ = d2DuhConst v w K * (4 * t ^ (1 / 4 : ℝ)) :=
      d2DuhMajor_int ht v w K

end Duhamel

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
