import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelHigher
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelDuhamel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Parabolic Hoermander estimate for the causal heat Hessian

This file proves the scalar directional kernel estimate needed before the
heat-specific Calderon--Zygmund step.  The proof is split at the parabolic
radius of the translation.  The early slab uses a first spatial moment of
`heatD2`; the late slab uses the actual derivatives `heatD3` and `heatD2Dt`.
No general singular-integral structure is introduced here.
-/

noncomputable section

open MeasureTheory Real Set Filter
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section FirstMoment

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

/-- First radial moment of the time-one Hessian majorant. -/
def baseD2One (x : V) : ℝ :=
  ‖x‖ * baseD2Maj x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2One_nonneg (x : V) : 0 ≤ baseD2One x :=
  mul_nonneg (norm_nonneg x) (baseD2Maj_nonneg x)

/-- Integrability of the first radial Hessian moment. -/
theorem baseD2One_int : Integrable (baseD2One : V → ℝ) := by
  have h3 := (gaussMoment_int (V := V) 3
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have h1 := (gaussMoment_int (V := V) 1
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have heq : baseD2One = fun x : V =>
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 3 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) +
        ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 1 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD2One baseD2Maj baseHeat
    ring
  rw [heq]
  exact h3.add h1

/-- Dimension-dependent first-moment constant for the heat Hessian. -/
def heatC2One (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD2One x

omit [Nontrivial V] in
theorem heatC2One_nonneg : 0 ≤ heatC2One V :=
  integral_nonneg baseD2One_nonneg

/-- Scaled first-moment Hessian majorant. -/
def heatD2One (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
    baseD2One ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2One_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatD2One t x := by
  unfold heatD2One
  exact mul_nonneg
    (mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (inv_nonneg.mpr (heatScale_pos ht).le))
    (baseD2One_nonneg _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The scaled first-moment majorant is exactly `norm x` times the ordinary
Hessian majorant. -/
theorem heatD2One_eq {t : ℝ} (ht : 0 < t) (x : V) :
    heatD2One t x = ‖x‖ * heatD2Maj t x := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hx : x = heatScale t • ((heatScale t)⁻¹ • x) := by
    simp [hr.ne']
  have hnorm : ‖x‖ = heatScale t * ‖(heatScale t)⁻¹ • x‖ := by
    calc
      ‖x‖ = ‖heatScale t • ((heatScale t)⁻¹ • x)‖ := congrArg norm hx
      _ = heatScale t * ‖(heatScale t)⁻¹ • x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  unfold heatD2One heatD2Maj baseD2One
  rw [hnorm]
  field_simp [hr.ne']

/-- Integrability of the scaled first-moment majorant. -/
theorem heatD2One_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatD2One t : V → ℝ) := by
  unfold heatD2One
  exact (baseD2One_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
/-- Exact spatial integral of the first-moment Hessian majorant. -/
theorem integral_heatD2One {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD2One t x = (heatScale t)⁻¹ * heatC2One V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatD2One heatC2One
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseD2One hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Pointwise Hessian bound after inserting one spatial moment. -/
theorem heatD2_one_bound {t : ℝ} (ht : 0 < t) (v w x : V) :
    ‖heatD2 t v w x‖ * ‖x‖ ≤ ‖v‖ * ‖w‖ * heatD2One t x := by
  rw [heatD2One_eq ht]
  calc
    ‖heatD2 t v w x‖ * ‖x‖ ≤
        (‖v‖ * ‖w‖ * heatD2Maj t x) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (heatD2_bound ht v w x) (norm_nonneg x)
    _ = ‖v‖ * ‖w‖ * (‖x‖ * heatD2Maj t x) := by ring

/-- The first-weighted spatial `L¹` norm of the Hessian. -/
theorem integral_oneD2 {t : ℝ} (ht : 0 < t) (v w : V) :
    (∫ x : V, ‖heatD2 t v w x‖ * ‖x‖) ≤
      ‖v‖ * ‖w‖ * (heatScale t)⁻¹ * heatC2One V := by
  have hmajor : Integrable
      (fun x : V => (‖v‖ * ‖w‖) * heatD2One t x) :=
    (heatD2One_int (V := V) ht).const_mul _
  have hleft : Integrable (fun x : V => ‖heatD2 t v w x‖ * ‖x‖) := by
    refine hmajor.mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
      fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (norm_nonneg x))]
      exact heatD2_one_bound ht v w x
  calc
    (∫ x : V, ‖heatD2 t v w x‖ * ‖x‖) ≤
        ∫ x : V, (‖v‖ * ‖w‖) * heatD2One t x :=
      integral_mono hleft hmajor (fun x => heatD2_one_bound ht v w x)
    _ = (‖v‖ * ‖w‖) * ((heatScale t)⁻¹ * heatC2One V) := by
      rw [integral_const_mul, integral_heatD2One ht]
    _ = ‖v‖ * ‖w‖ * (heatScale t)⁻¹ * heatC2One V := by ring

end FirstMoment

section EarlyTail

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

/-- Exterior of the spatial ball of radius `R`, with the boundary included. -/
def d2TailSet (R : ℝ) : Set V :=
  {x | R ≤ ‖x‖}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V] in
theorem d2TailSet_meas (R : ℝ) : MeasurableSet (d2TailSet (V := V) R) := by
  exact measurableSet_le measurable_const continuous_norm.measurable

/-- A first moment controls the Hessian mass outside a positive radius. -/
theorem heatD2_tail {t R : ℝ} (ht : 0 < t) (hR : 0 < R) (v w : V) :
    (∫ x : V in d2TailSet R, ‖heatD2 t v w x‖) ≤
      R⁻¹ * ‖v‖ * ‖w‖ * (heatScale t)⁻¹ * heatC2One V := by
  let A : ℝ := R⁻¹ * (‖v‖ * ‖w‖)
  have hA : 0 ≤ A := mul_nonneg (inv_nonneg.mpr hR.le)
    (mul_nonneg (norm_nonneg v) (norm_nonneg w))
  have hleft : IntegrableOn (fun x : V => ‖heatD2 t v w x‖) (d2TailSet R) :=
    (heatD2_int ht v w).norm.integrableOn
  have hmajor : Integrable (fun x : V => A * heatD2One t x) :=
    (heatD2One_int (V := V) ht).const_mul _
  have hpoint : (fun x : V => ‖heatD2 t v w x‖) ≤ᵐ[
      (volume : Measure V).restrict (d2TailSet R)]
      (fun x : V => A * heatD2One t x) := by
    filter_upwards [ae_restrict_mem (d2TailSet_meas (V := V) R)] with x hx
    have hxR : R ≤ ‖x‖ := hx
    calc
      ‖heatD2 t v w x‖ = R⁻¹ * (R * ‖heatD2 t v w x‖) := by
        field_simp [hR.ne']
      _ ≤ R⁻¹ * (‖heatD2 t v w x‖ * ‖x‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
        nlinarith [norm_nonneg (heatD2 t v w x)]
      _ ≤ R⁻¹ * (‖v‖ * ‖w‖ * heatD2One t x) := by
        exact mul_le_mul_of_nonneg_left (heatD2_one_bound ht v w x)
          (inv_nonneg.mpr hR.le)
      _ = A * heatD2One t x := by ring
  calc
    (∫ x : V in d2TailSet R, ‖heatD2 t v w x‖) ≤
        ∫ x : V in d2TailSet R, A * heatD2One t x :=
      integral_mono_ae hleft (hmajor.integrableOn) hpoint
    _ ≤ ∫ x : V, A * heatD2One t x := by
      exact integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun x => mul_nonneg hA (heatD2One_nonneg ht x)) hmajor
    _ = A * ((heatScale t)⁻¹ * heatC2One V) := by
      rw [integral_const_mul, integral_heatD2One ht]
    _ = R⁻¹ * ‖v‖ * ‖w‖ * (heatScale t)⁻¹ * heatC2One V := by
      simp only [A]
      ring

end EarlyTail

section IntegratedTail

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

/-- The early-time Hessian mass outside a fixed spatial ball.  The time
singularity is exactly integrable and leaves the scale-invariant factor
`sqrt T / R`. -/
theorem heatD2_tail_time {T R : ℝ} (hT : 0 < T) (hR : 0 < R) (v w : V) :
    (∫ t : ℝ in Set.Ioc 0 T,
      ∫ x : V in d2TailSet R, ‖heatD2 t v w x‖) ≤
      2 * R⁻¹ * ‖v‖ * ‖w‖ * T ^ (1 / 2 : ℝ) * heatC2One V := by
  let A : ℝ := R⁻¹ * ‖v‖ * ‖w‖ * heatC2One V
  let F : ℝ × V → ℝ := fun z => ‖heatD2 z.1 v w z.2‖
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 T)
  let ν : Measure V := volume.restrict (d2TailSet R)
  have hpow : IntervalIntegrable heatScale12 volume 0 T := by
    unfold heatScale12
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpow' : Integrable heatScale12 μ := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hpow
  have hscale : ∫ t : ℝ in 0..T, heatScale12 t =
      2 * T ^ (1 / 2 : ℝ) := by
    unfold heatScale12
    rw [integral_rpow (Or.inl (by norm_num))]
    have hexp : -(1 : ℝ) / 2 + 1 = 1 / 2 := by ring
    rw [hexp, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    ring
  have hmajor : Integrable (fun t : ℝ => A * heatScale12 t) μ :=
    hpow'.const_mul A
  have hFmeas : AEStronglyMeasurable F (μ.prod ν) := by
    apply Measurable.aestronglyMeasurable
    unfold F heatD2 baseD2 baseHeat baseHeatMass heatScale
    fun_prop
  have hslice_meas : AEStronglyMeasurable
      (fun t : ℝ => ∫ x : V, F (t, x) ∂ν) μ :=
    hFmeas.integral_prod_right'
  have hleft : Integrable (fun t : ℝ => ∫ x : V, F (t, x) ∂ν) μ := by
    refine hmajor.mono' hslice_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have hslice_nonneg : 0 ≤ ∫ x : V, F (t, x) ∂ν :=
      integral_nonneg (fun _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hslice_nonneg]
    calc
      (∫ x : V, F (t, x) ∂ν) =
          ∫ x : V in d2TailSet R, ‖heatD2 t v w x‖ := by
        rfl
      _ ≤ R⁻¹ * ‖v‖ * ‖w‖ * (heatScale t)⁻¹ * heatC2One V :=
        heatD2_tail ht0 hR v w
      _ = A * heatScale12 t := by
        rw [heatScale12_eq ht0]
        simp only [A]
        ring
  calc
    (∫ t : ℝ in Set.Ioc 0 T,
        ∫ x : V in d2TailSet R, ‖heatD2 t v w x‖) =
        ∫ t : ℝ, (∫ x : V, F (t, x) ∂ν) ∂μ := by
      rfl
    _ ≤ ∫ t : ℝ, A * heatScale12 t ∂μ :=
      integral_mono_ae hleft hmajor (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact heatD2_tail ht.1 hR v w |>.trans_eq (by
          rw [heatScale12_eq ht.1]
          simp only [A]
          ring))
    _ = A * (2 * T ^ (1 / 2 : ℝ)) := by
      rw [MeasureTheory.integral_const_mul]
      change A * (∫ t : ℝ in Set.Ioc 0 T, heatScale12 t) = _
      rw [← intervalIntegral.integral_of_le hT.le, hscale]
    _ = 2 * R⁻¹ * ‖v‖ * ‖w‖ * T ^ (1 / 2 : ℝ) * heatC2One V := by
      simp only [A]
      ring

end IntegratedTail

section FarSpace

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

/-- Integrability of the norm of the third spatial heat-kernel derivative. -/
theorem heatD3_norm_int {t : ℝ} (ht : 0 < t) (u v w : V) :
    Integrable (fun x : V => ‖heatD3 t u v w x‖) := by
  refine ((heatD3Maj_int (V := V) ht).const_mul
    (‖u‖ * ‖v‖ * ‖w‖)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  · filter_upwards with x
    simpa [mul_assoc] using heatD3_bound ht u v w x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Pointwise segment estimate for a spatial translate of `heatD2`. -/
private theorem d2Space_point {t : ℝ} (ht : 0 < t)
    (h v w x : V) :
    ‖heatD2 t v w (x - h) - heatD2 t v w x‖ ≤
      ∫ s : ℝ in Set.Ioc 0 1,
        ‖heatD3 t h v w (x + s • (-h))‖ := by
  let γ : ℝ → V := fun s => x + s • (-h)
  have hγ : ∀ s : ℝ, HasDerivAt γ (-h) s := by
    intro s
    have hs : HasDerivAt (fun r : ℝ => r • (-h)) (-h) s := by
      simpa using (hasDerivAt_id s).smul_const (-h)
    simpa only [γ] using hs.const_add x
  have hcomp : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => heatD2 t v w (γ r))
        (-heatD3 t h v w (γ s)) s := by
    intro s
    have h0 := (heatD2_hasFDeriv (t := t) ht v w (γ s)).comp_hasDerivAt s (hγ s)
    convert h0 using 1
    simp only [heatD3Map_apply]
    simp [heatD3, baseD3]
    ring
  have hderiv : IntervalIntegrable
      (fun s : ℝ => -heatD3 t h v w (γ s)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold γ heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  have hftc :
      (∫ s : ℝ in 0..1, -heatD3 t h v w (γ s)) =
        heatD2 t v w (γ 1) - heatD2 t v w (γ 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hcomp s) hderiv
  have hγ0 : γ 0 = x := by simp [γ]
  have hγ1 : γ 1 = x - h := by simp [γ, sub_eq_add_neg]
  calc
    ‖heatD2 t v w (x - h) - heatD2 t v w x‖ =
        ‖∫ s : ℝ in 0..1, -heatD3 t h v w (γ s)‖ := by
      rw [hftc, hγ1, hγ0]
    _ ≤ ∫ s : ℝ in 0..1, ‖-heatD3 t h v w (γ s)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ s : ℝ in Set.Ioc 0 1,
        ‖heatD3 t h v w (x + s • (-h))‖ := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply integral_congr_ae
      filter_upwards with s
      simp only [norm_neg, γ]

/-- Spatial translation estimate at a fixed positive time.  This is the
space arm of the late Hoermander path. -/
theorem heatD2_space_diff {t : ℝ} (ht : 0 < t) (h v w : V) :
    (∫ x : V, ‖heatD2 t v w (x - h) - heatD2 t v w x‖) ≤
      ‖h‖ * ‖v‖ * ‖w‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let G : ℝ × V → ℝ := fun z =>
    ‖heatD3 t h v w (z.2 + z.1 • (-h))‖
  have hbase := heatD3_norm_int (V := V) ht h v w
  have hslice_int : ∀ s : ℝ,
      Integrable (fun x : V => G (s, x)) := by
    intro s
    simpa only [G, add_comm] using hbase.comp_add_left (s • (-h))
  have hslice_eq : ∀ s : ℝ,
      (∫ x : V, G (s, x)) = ∫ x : V, ‖heatD3 t h v w x‖ := by
    intro s
    simpa only [G] using integral_add_right_eq_self
      (fun x : V => ‖heatD3 t h v w x‖) (s • (-h))
  have hGmeas : AEStronglyMeasurable G (μ.prod (volume : Measure V)) := by
    apply Continuous.aestronglyMeasurable
    unfold G heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  have houter : Integrable (fun s : ℝ => ∫ x : V, ‖G (s, x)‖) μ := by
    have hconst : IntegrableOn
        (fun _ : ℝ => ∫ x : V, ‖heatD3 t h v w x‖) (Set.Ioc 0 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have heq : (fun s : ℝ => ∫ x : V, ‖G (s, x)‖) =
        fun _ : ℝ => ∫ x : V, ‖heatD3 t h v w x‖ := by
      funext s
      rw [integral_congr_ae (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])]
      exact hslice_eq s
    simpa only [μ, heq] using hconst
  have hGint : Integrable G (μ.prod (volume : Measure V)) := by
    exact (integrable_prod_iff hGmeas).2
      ⟨Eventually.of_forall hslice_int, houter⟩
  have hleft : Integrable
      (fun x : V => ‖heatD2 t v w (x - h) - heatD2 t v w x‖) := by
    have h0 := (heatD2_int ht v w).norm
    have h1 : Integrable (fun x : V => ‖heatD2 t v w (x - h)‖) := by
      simpa [sub_eq_add_neg] using h0.comp_add_right (-h)
    exact (h1.add h0).mono' (by
      apply Continuous.aestronglyMeasurable
      unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
      fun_prop) (by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact norm_sub_le _ _)
  have hright : Integrable (fun x : V => ∫ s : ℝ, G (s, x) ∂μ) :=
    hGint.integral_prod_right
  calc
    (∫ x : V, ‖heatD2 t v w (x - h) - heatD2 t v w x‖) ≤
        ∫ x : V, ∫ s : ℝ, G (s, x) ∂μ := by
      exact integral_mono hleft hright (fun x => by
        simpa only [μ, G] using d2Space_point ht h v w x)
    _ = ∫ s : ℝ, (∫ x : V, G (s, x)) ∂μ := by
      exact (integral_integral_swap
        (f := fun s x => G (s, x)) hGint).symm
    _ = ∫ s : ℝ, (∫ x : V, ‖heatD3 t h v w x‖) ∂μ := by
      apply integral_congr_ae
      filter_upwards with s
      exact hslice_eq s
    _ = ∫ x : V, ‖heatD3 t h v w x‖ := by
      simp only [μ, setIntegral_const]
      rw [Real.volume_real_Ioc_of_le (by norm_num), sub_zero, one_smul]
    _ ≤ ‖h‖ * ‖v‖ * ‖w‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V :=
      integral_norm_D3 ht h v w

end FarSpace

section FarTime

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

/-- Integrability of the norm of the Hessian time derivative. -/
theorem heatD2Dt_norm_int {t : ℝ} (ht : 0 < t) (v w : V) :
    Integrable (fun x : V => ‖heatD2Dt t v w x‖) := by
  refine ((heatD2DtMaj_int (V := V) ht).const_mul (‖v‖ * ‖w‖)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold heatD2Dt baseD2Dt baseD2 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  · filter_upwards with x
    simpa [mul_assoc] using heatD2Dt_bound ht v w x

omit [MeasurableSpace V] [BorelSpace V] in
/-- Every point on the time segment from `t` to `t-a` remains above
`t - |a|`. -/
private theorem timeSeg_lower {t a s : ℝ} (hta : |a| < t)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 < t - |a| ∧ t - |a| ≤ t - s * a := by
  have hsa : s * a ≤ |a| := by
    calc
      s * a ≤ |s * a| := le_abs_self _
      _ = s * |a| := by rw [abs_mul, abs_of_nonneg hs.1]
      _ ≤ 1 * |a| := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg a)
      _ = |a| := one_mul _
  exact ⟨sub_pos.mpr hta, sub_le_sub_left hsa t⟩

omit [MeasurableSpace V] [BorelSpace V] in
/-- Pointwise segment estimate for a time translate of `heatD2`. -/
private theorem d2Time_point {t a : ℝ} (hta : |a| < t)
    (v w x : V) :
    ‖heatD2 (t - a) v w x - heatD2 t v w x‖ ≤
      ∫ s : ℝ in Set.Ioc 0 1,
        |a| * ‖heatD2Dt (t - s * a) v w x‖ := by
  let γ : ℝ → ℝ := fun s => t - s * a
  have hγ : ∀ s : ℝ, HasDerivAt γ (-a) s := by
    intro s
    simpa only [γ, Pi.sub_apply, id_eq, zero_sub, one_mul] using (hasDerivAt_const s t).sub
      ((hasDerivAt_id s).mul_const a)
  have hcomp : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => heatD2 (γ r) v w x)
        (-a * heatD2Dt (γ s) v w x) s := by
    intro s hs
    have hpos : 0 < γ s := (timeSeg_lower hta hs).1.trans_le
      (timeSeg_lower hta hs).2
    have h0 := (heatD2_time hpos v w x).comp s (hγ s)
    convert h0 using 1
    all_goals ring
  have hderiv : IntervalIntegrable
      (fun s : ℝ => -a * heatD2Dt (γ s) v w x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hpos : 0 < γ s := (timeSeg_lower hta hs).1.trans_le
      (timeSeg_lower hta hs).2
    have hγne : γ s ≠ 0 := hpos.ne'
    have hrne : heatScale (γ s) ≠ 0 := (heatScale_pos hpos).ne'
    have hpowne : heatScale (γ s) ^ Module.finrank ℝ V ≠ 0 :=
      pow_ne_zero _ hrne
    have hsqne : (γ s) ^ 2 ≠ 0 := pow_ne_zero _ hγne
    have hderiv_cont : ContinuousAt
        (fun r : ℝ => heatD2Dt (γ r) v w x) s := by
      unfold heatD2Dt baseD2Dt baseD2 baseD3 baseHeat baseHeatMass heatScale γ
      fun_prop (disch := assumption)
    exact continuousAt_const.mul hderiv_cont |>.continuousWithinAt
  have hftc :
      (∫ s : ℝ in 0..1, -a * heatD2Dt (γ s) v w x) =
        heatD2 (γ 1) v w x - heatD2 (γ 0) v w x := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hcomp s (by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs)) hderiv
  have hγ0 : γ 0 = t := by simp [γ]
  have hγ1 : γ 1 = t - a := by simp [γ]
  calc
    ‖heatD2 (t - a) v w x - heatD2 t v w x‖ =
        ‖∫ s : ℝ in 0..1, -a * heatD2Dt (γ s) v w x‖ := by
      rw [hftc, hγ1, hγ0]
    _ ≤ ∫ s : ℝ in 0..1, ‖-a * heatD2Dt (γ s) v w x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ∫ s : ℝ in Set.Ioc 0 1,
        |a| * ‖heatD2Dt (t - s * a) v w x‖ := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply integral_congr_ae
      filter_upwards with s
      simp only [Real.norm_eq_abs, abs_mul, abs_neg, γ]

/-- Time translation estimate at a fixed time which stays on the causal
side.  This is the time arm of the late Hoermander path. -/
theorem heatD2_time_diff {t a : ℝ} (hta : |a| < t) (v w : V) :
    (∫ x : V, ‖heatD2 (t - a) v w x - heatD2 t v w x‖) ≤
      |a| * ‖v‖ * ‖w‖ * ((t - |a|) ^ 2)⁻¹ * heatC2Dt V := by
  let d : ℝ := t - |a|
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let G : ℝ × V → ℝ := fun z =>
    |a| * ‖heatD2Dt (t - z.1 * a) v w z.2‖
  have hd : 0 < d := sub_pos.mpr hta
  have hslice_pos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < t - s * a := by
    intro s hs
    exact (timeSeg_lower hta hs).1.trans_le (timeSeg_lower hta hs).2
  have hslice_int : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun x : V => G (s, x)) := by
    intro s hs
    exact (heatD2Dt_norm_int (V := V) (hslice_pos s hs) v w).const_mul |a|
  have hslice_le : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∫ x : V, G (s, x)) ≤
        |a| * ‖v‖ * ‖w‖ * (d ^ 2)⁻¹ * heatC2Dt V := by
    intro s hs
    have hlow := (timeSeg_lower hta hs).2
    have hspos := hslice_pos s hs
    have hsq : d ^ 2 ≤ (t - s * a) ^ 2 :=
      (sq_le_sq₀ hd.le hspos.le).2 hlow
    have hinv : ((t - s * a) ^ 2)⁻¹ ≤ (d ^ 2)⁻¹ :=
      (inv_le_inv₀ (sq_pos_of_pos hspos) (sq_pos_of_pos hd)).2 hsq
    calc
      (∫ x : V, G (s, x)) =
          |a| * ∫ x : V, ‖heatD2Dt (t - s * a) v w x‖ := by
        rw [integral_const_mul]
      _ ≤ |a| *
          (‖v‖ * ‖w‖ * ((t - s * a) ^ 2)⁻¹ * heatC2Dt V) := by
        exact mul_le_mul_of_nonneg_left
          (integral_norm_D2Dt (hslice_pos s hs) v w) (abs_nonneg a)
      _ ≤ |a| * (‖v‖ * ‖w‖ * (d ^ 2)⁻¹ * heatC2Dt V) := by
        gcongr
        exact heatC2Dt_nonneg
      _ = |a| * ‖v‖ * ‖w‖ * (d ^ 2)⁻¹ * heatC2Dt V := by ring
  have hGmeas : AEStronglyMeasurable G (μ.prod (volume : Measure V)) := by
    apply Measurable.aestronglyMeasurable
    unfold G heatD2Dt baseD2Dt baseD2 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  have houter : Integrable (fun s : ℝ => ∫ x : V, ‖G (s, x)‖) μ := by
    let C : ℝ := |a| * ‖v‖ * ‖w‖ * (d ^ 2)⁻¹ * heatC2Dt V
    have hC : 0 ≤ C := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (abs_nonneg a) (norm_nonneg v)) (norm_nonneg w))
          (inv_nonneg.mpr (sq_nonneg d))) heatC2Dt_nonneg
    have hconst : IntegrableOn (fun _ : ℝ => C) (Set.Ioc 0 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine hconst.mono' ?_ ?_
    · exact hGmeas.norm.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
      have hnormeq : (∫ x : V, ‖G (s, x)‖) = ∫ x : V, G (s, x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg (abs_nonneg a) (norm_nonneg _)
      have hintnonneg : 0 ≤ ∫ x : V, ‖G (s, x)‖ :=
        integral_nonneg (fun _ => norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hintnonneg, hnormeq]
      simpa only [C, d] using hslice_le s hs'
  have hGint : Integrable G (μ.prod (volume : Measure V)) := by
    apply (integrable_prod_iff hGmeas).2
    refine ⟨?_, houter⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hslice_int s ⟨hs.1.le, hs.2⟩
  have htma : 0 < t - a := by
    have hale : a ≤ |a| := le_abs_self a
    linarith
  have ht : 0 < t := (abs_nonneg a).trans_lt hta
  have hleft : Integrable
      (fun x : V => ‖heatD2 (t - a) v w x - heatD2 t v w x‖) := by
    exact ((heatD2_int htma v w).sub (heatD2_int ht v w)).norm
  have hright : Integrable (fun x : V => ∫ s : ℝ, G (s, x) ∂μ) :=
    hGint.integral_prod_right
  calc
    (∫ x : V, ‖heatD2 (t - a) v w x - heatD2 t v w x‖) ≤
        ∫ x : V, ∫ s : ℝ, G (s, x) ∂μ := by
      exact integral_mono hleft hright (fun x => by
        simpa only [μ, G] using d2Time_point hta v w x)
    _ = ∫ s : ℝ, (∫ x : V, G (s, x)) ∂μ := by
      exact (integral_integral_swap
        (f := fun s x => G (s, x)) hGint).symm
    _ ≤ ∫ _s : ℝ, (|a| * ‖v‖ * ‖w‖ *
        (d ^ 2)⁻¹ * heatC2Dt V) ∂μ := by
      exact integral_mono_ae hGint.integral_prod_left
        ((integrableOn_const measure_Ioc_lt_top.ne)) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact hslice_le s ⟨hs.1.le, hs.2⟩)
    _ = |a| * ‖v‖ * ‖w‖ * (d ^ 2)⁻¹ * heatC2Dt V := by
      simp only [μ, setIntegral_const]
      rw [Real.volume_real_Ioc_of_le (by norm_num), sub_zero, one_smul]
    _ = |a| * ‖v‖ * ‖w‖ * ((t - |a|) ^ 2)⁻¹ * heatC2Dt V := by
      rfl

end FarTime

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
