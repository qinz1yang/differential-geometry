import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelSup
import Mathlib.Topology.MetricSpace.HolderNorm

/-!
# Quantitative approximation by the Euclidean heat kernel

The boundary term in the Duhamel identity is genuine only after proving that
the heat kernel converges to the identity.  For the half-Holder spatial data
used by the low-regularity parametrix, the first half moment of the Gaussian
gives the explicit rate `t^(1/4)`.
-/

noncomputable section

open MeasureTheory Real
open scoped RealInnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section HalfMoment

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

/-- The half spatial moment of the time-one heat kernel. -/
def baseHeatHalf (x : V) : ℝ :=
  Real.sqrt ‖x‖ * baseHeat x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseHeatHalf_nonneg (x : V) : 0 ≤ baseHeatHalf x := by
  unfold baseHeatHalf
  exact mul_nonneg (Real.sqrt_nonneg _) (baseHeat_nonneg x)

private theorem baseHeatFirst_int :
    Integrable (fun x : V => ‖x‖ * baseHeat x) := by
  have h := (gaussMoment_int (V := V) 1
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul (baseHeatMass V)⁻¹
  have heq : (fun x : V => ‖x‖ * baseHeat x) = fun x : V =>
      (baseHeatMass V)⁻¹ *
        (‖x‖ ^ 1 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseHeat
    ring
  rw [heq]
  exact h

/-- The first half moment of the normalized Gaussian is finite. -/
theorem baseHeatHalf_int : Integrable (baseHeatHalf : V → ℝ) := by
  have hmajor : Integrable (fun x : V => (1 + ‖x‖) * baseHeat x) := by
    have h := (baseHeat_int (V := V)).add (baseHeatFirst_int (V := V))
    have heq : (fun x : V => (1 + ‖x‖) * baseHeat x) =
        fun x : V => baseHeat x + ‖x‖ * baseHeat x := by
      funext x
      ring
    rw [heq]
    exact h
  refine hmajor.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold baseHeatHalf baseHeat baseHeatMass
    fun_prop
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (baseHeatHalf_nonneg x)]
  have hsqrt : Real.sqrt ‖x‖ ≤ 1 + ‖x‖ := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [norm_nonneg x]⟩
  exact mul_le_mul_of_nonneg_right hsqrt (baseHeat_nonneg x)

/-- Dimension-dependent half moment of the time-one heat kernel. -/
def heatC0Half (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseHeatHalf x

omit [Nontrivial V] in
theorem heatC0Half_nonneg : 0 ≤ heatC0Half V :=
  integral_nonneg baseHeatHalf_nonneg

/-- Scaled half-moment density for the positive-time heat kernel. -/
def heatHalf (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * Real.sqrt (heatScale t) *
    baseHeatHalf ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatHalf_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatHalf t x := by
  unfold heatHalf
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (Real.sqrt_nonneg _))
    (baseHeatHalf_nonneg _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The scaled density is exactly `sqrt ‖x‖` times the heat kernel. -/
theorem heatHalf_eq {t : ℝ} (ht : 0 < t) (x : V) :
    heatHalf t x = Real.sqrt ‖x‖ * heatKernel t x := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hx : x = heatScale t • ((heatScale t)⁻¹ • x) := by
    simp [hr.ne']
  have hsqrt : Real.sqrt ‖x‖ =
      Real.sqrt (heatScale t) * Real.sqrt ‖(heatScale t)⁻¹ • x‖ := by
    calc
      Real.sqrt ‖x‖ = Real.sqrt ‖heatScale t • ((heatScale t)⁻¹ • x)‖ :=
        congrArg (fun z : V => Real.sqrt ‖z‖) hx
      _ = Real.sqrt (heatScale t * ‖(heatScale t)⁻¹ • x‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = Real.sqrt (heatScale t) * Real.sqrt ‖(heatScale t)⁻¹ • x‖ :=
        Real.sqrt_mul hr.le _
  unfold heatHalf heatKernel baseHeatHalf
  rw [hsqrt]
  ring

theorem heatHalf_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatHalf t : V → ℝ) := by
  unfold heatHalf
  exact (baseHeatHalf_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
/-- Exact scaling of the first half moment. -/
theorem integral_heatHalf {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatHalf t x = Real.sqrt (heatScale t) * heatC0Half V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatHalf heatC0Half
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseHeatHalf hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

end HalfMoment

section ApproxIdentity

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
private theorem holder_half {K : ℝ≥0} {u : V → F}
    (hu : HolderWith K (1 / 2 : ℝ≥0) u) (x y : V) :
    ‖u (x - y) - u x‖ ≤ (K : ℝ) * Real.sqrt ‖y‖ := by
  have hxy : dist (x - y) x = ‖y‖ := by
    rw [dist_eq_norm]
    have : (x - y) - x = -y := by abel
    rw [this, norm_neg]
  have h := hu.dist_le (x - y) x
  rw [dist_eq_norm, hxy] at h
  simpa [Real.sqrt_eq_rpow] using h

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
private theorem approx_integrand {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    {u : V → F} (hu : HolderWith K (1 / 2 : ℝ≥0) u) (x y : V) :
    ‖heatKernel t y • (u (x - y) - u x)‖ ≤
      (K : ℝ) * heatHalf t y := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht y)]
  calc
    heatKernel t y * ‖u (x - y) - u x‖
        ≤ heatKernel t y * ((K : ℝ) * Real.sqrt ‖y‖) :=
      mul_le_mul_of_nonneg_left (holder_half hu x y) (heatKernel_nonneg ht y)
    _ = (K : ℝ) * heatHalf t y := by
      rw [heatHalf_eq ht]
      ring

/-- Quantitative approximate-identity estimate on global half-Holder data.
The factor `sqrt (sqrt t)` is `t^(1/4)`. -/
theorem heatSup_id_norm {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    {u : BoundedContinuousFunction V F} (hu : HolderWith K (1 / 2 : ℝ≥0) u) (x : V) :
    ‖heatSup t u x - u x‖ ≤
      (K : ℝ) * Real.sqrt (heatScale t) * heatC0Half V := by
  have hdiff : Integrable
      (fun y : V => heatKernel t y • (u (x - y) - u x)) := by
    refine ((heatHalf_int (V := V) ht).const_mul (K : ℝ)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold heatKernel baseHeat baseHeatMass heatScale
      fun_prop
    filter_upwards with y
    exact approx_integrand ht hu x y
  have hraw := supKernel_int (heatKernel_int (V := V) ht) u x
  have hconst := (heatKernel_int (V := V) ht).smul_const (u x)
  have heq : heatSup t u x - u x =
      ∫ y : V, heatKernel t y • (u (x - y) - u x) := by
    unfold heatSup supKernel
    calc
      (∫ y : V, heatKernel t y • u (x - y)) - u x =
          (∫ y : V, heatKernel t y • u (x - y)) -
            ∫ y : V, heatKernel t y • u x := by
        rw [integral_smul_const, integral_heatKernel ht, one_smul]
      _ = ∫ y : V,
          heatKernel t y • u (x - y) - heatKernel t y • u x :=
        (integral_sub hraw hconst).symm
      _ = ∫ y : V, heatKernel t y • (u (x - y) - u x) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [smul_sub]
  rw [heq]
  calc
    ‖∫ y : V, heatKernel t y • (u (x - y) - u x)‖
        ≤ ∫ y : V, (K : ℝ) * heatHalf t y :=
      norm_integral_le_of_norm_le ((heatHalf_int (V := V) ht).const_mul (K : ℝ))
        (Filter.Eventually.of_forall fun y => approx_integrand ht hu x y)
    _ = (K : ℝ) * (Real.sqrt (heatScale t) * heatC0Half V) := by
      rw [integral_const_mul, integral_heatHalf ht]
    _ = (K : ℝ) * Real.sqrt (heatScale t) * heatC0Half V := by ring

end ApproxIdentity

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
