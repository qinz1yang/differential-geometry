import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LocallyLipschitz

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a T : ℝ}

def zeroDuhamelCross (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    CrossScaleField (I := I) (M := M) g r s a T :=
  maximalRegularityRecentredCrossScaleField (I := I) (M := M)
    (h_compact := h_compact) hT 0 f

omit [NeZero (Module.finrank ℝ E)] in
theorem zeroRepr_zero (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    (zeroDuhamelCross (I := I) (M := M) hT h_compact f).repr 0 =
      (0 : TensorHs (I := I) (M := M) g r s (a + 1)) := by
  simpa only [zeroDuhamelCross] using
    recentred_repr_zero (I := I) (M := M)
      (h_compact := h_compact) hT
      (0 : TensorHs (I := I) (M := M) g r s (a + 2)) f

omit [NeZero (Module.finrank ℝ E)] in
theorem zeroRepr_ae (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    (fun t => (zeroDuhamelCross (I := I) (M := M)
        hT h_compact f).repr t) =ᵐ[timeMeasure T]
      fun t => maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M)
        a hT 0 f t := by
  have h := recentred_repr_eq_field_sub (I := I) (M := M)
    (h_compact := h_compact) hT hT1
    (0 : TensorHs (I := I) (M := M) g r s (a + 2)) f
  filter_upwards [h] with t ht
  simpa only [zeroDuhamelCross, map_zero, sub_zero] using ht

omit [NeZero (Module.finrank ℝ E)] in
theorem zeroRepr_meas (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    AEStronglyMeasurable
      (fun t => (zeroDuhamelCross (I := I) (M := M)
        hT h_compact f).repr t)
      (timeMeasure T) := by
  exact (Lp.aestronglyMeasurable
    (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M)
      a hT (0 : TensorHs (I := I) (M := M) g r s (a + 2)) f)).congr
        (zeroRepr_ae (I := I) (M := M) hT hT1 h_compact f).symm

omit [NeZero (Module.finrank ℝ E)] in
private theorem homMode_zero (hT : 0 < T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : TensorHs (I := I) (M := M) g r s (a + 2)) i = 0 := by
  have hsq := norm_homModeCoeff_sq_le (I := I) (M := M)
    (a := a) (T := T) hT.le
    (0 : TensorHs (I := I) (M := M) g r s (a + 2)) i
  rw [TensorHs.zero_coeff] at hsq
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg
    (homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : TensorHs (I := I) (M := M) g r s (a + 2)) i)]

omit [NeZero (Module.finrank ℝ E)] in
private theorem homField_zero (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    maximalRegularityHomogeneousSolutionFieldTraceScale (I := I) (M := M) a T
        (0 : TensorHs (I := I) (M := M) g r s (a + 2)) = 0 := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maximalRegularityHomogeneousSolutionFieldHa1_timeModeCoeff (I := I) (M := M)
    (a := a) (T := T) hT.le, homMode_zero (I := I) (M := M) hT i]
  simp only [timeModeCoeff, map_zero]

omit [NeZero (Module.finrank ℝ E)] in
private theorem duhamelField_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT 0 f -
        maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT 0 f' =
      maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT 0 (f - f') := by
  rw [maximalRegularityDuhamelSolutionFieldHa1_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1]
  rw [maximalRegularityDuhamelSolutionFieldHa1,
    homField_zero (I := I) (M := M) (a := a) hT h_compact, zero_add]

omit [NeZero (Module.finrank ℝ E)] in
theorem zeroRepr_sub_ae (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    (fun t =>
      (zeroDuhamelCross (I := I) (M := M) hT h_compact f).repr t -
        (zeroDuhamelCross (I := I) (M := M) hT h_compact f').repr t)
      =ᵐ[timeMeasure T]
    fun t =>
      (zeroDuhamelCross (I := I) (M := M)
        hT h_compact (f - f')).repr t := by
  have hf := zeroRepr_ae (I := I) (M := M) hT hT1 h_compact f
  have hf' := zeroRepr_ae (I := I) (M := M) hT hT1 h_compact f'
  have hd := zeroRepr_ae (I := I) (M := M) hT hT1 h_compact (f - f')
  have hsub := Lp.coeFn_sub
    (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT 0 f)
    (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT 0 f')
  rw [duhamelField_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 f f'] at hsub
  filter_upwards [hf, hf', hd, hsub] with t hft hf't hdt hst
  rw [hft, hf't, hdt]
  exact hst.symm

omit [NeZero (Module.finrank ℝ E)] in
theorem zeroRepr_norm_le (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖(zeroDuhamelCross (I := I) (M := M)
        hT h_compact f).repr t‖ ≤
      2 * Real.sqrt (1 + T) * ‖f‖ := by
  set u := zeroDuhamelCross (I := I) (M := M)
    hT h_compact f with hu
  have hsq := u.normSq_repr_le_initial_add_integral hT ht
  have hzero : u.repr 0 =
      (0 : TensorHs (I := I) (M := M) g r s (a + 1)) := by
    simpa only [hu] using
      zeroRepr_zero (I := I) (M := M) hT h_compact f
  rw [hzero, norm_zero, zero_pow (by norm_num), zero_add] at hsq
  have hhi : ‖u.hiL2‖ ≤ (1 + T) * ‖f‖ := by
    rw [hu]
    change ‖recentredHiL2 (I := I) (M := M) hT
      (0 : TensorHs (I := I) (M := M) g r s (a + 2)) f‖ ≤ (1 + T) * ‖f‖
    have h := recentredHi_norm_le (I := I) (M := M)
      (h_compact := h_compact) hT
      (0 : TensorHs (I := I) (M := M) g r s (a + 2)) f
    simpa only [norm_zero, mul_zero, zero_add] using h
  have hderiv : ‖u.lo.deriv‖ ≤ 2 * ‖f‖ := by
    rw [hu]
    change ‖(recentredCarrier (I := I) (M := M) hT
      (0 : TensorHs (I := I) (M := M) g r s (a + 2)) f).deriv‖ ≤ 2 * ‖f‖
    rw [recentredCarrier, TimeSobolev.timeH1.deriv_mk]
    have h := recentredCarrier_deriv_norm_le (I := I) (M := M)
      (h_compact := h_compact) hT
      (0 : TensorHs (I := I) (M := M) g r s (a + 2)) f
    simpa only [norm_zero, mul_zero, zero_add] using h
  have hmul :
      ‖u.hiL2‖ * ‖u.lo.deriv‖ ≤
        ((1 + T) * ‖f‖) * (2 * ‖f‖) :=
    mul_le_mul hhi hderiv (norm_nonneg _) (by positivity)
  have hholder :
      (∫ s in Set.Icc (0 : ℝ) T, ‖u.hiL2 s‖ * ‖u.lo.deriv s‖) ≤
        ‖u.hiL2‖ * ‖u.lo.deriv‖ := by
    have hhiLp : MemLp (fun s => ‖u.hiL2 s‖) (ENNReal.ofReal 2) (timeMeasure T) := by
      convert (Lp.memLp u.hiL2).norm using 1; norm_num
    have hloLp : MemLp (fun s => ‖u.lo.deriv s‖) (ENNReal.ofReal 2) (timeMeasure T) := by
      convert (Lp.memLp u.lo.deriv).norm using 1; norm_num
    have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := timeMeasure T) (f := fun s => ‖u.hiL2 s‖)
      (g := fun s => ‖u.lo.deriv s‖) Real.HolderConjugate.two_two
      hhiLp hloLp
    rw [TimeSobolev.norm_eq_sqrt_integral,
      TimeSobolev.norm_eq_sqrt_integral, Real.sqrt_eq_rpow,
      Real.sqrt_eq_rpow]
    simpa only [timeMeasure, norm_norm, Real.rpow_two] using h
  have hcross :
      (∫ s in (0 : ℝ)..t, 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖)) ≤
        2 * (‖u.hiL2‖ * ‖u.lo.deriv‖) := by
    rw [intervalIntegral.integral_of_le ht.1]
    calc
      (∫ s in Set.Ioc (0 : ℝ) t, 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖))
          ≤ ∫ s in Set.Icc (0 : ℝ) T, 2 * (‖u.hiL2 s‖ * ‖u.lo.deriv s‖) := by
            refine setIntegral_mono_set u.integrableOn_energyBound
              (Eventually.of_forall fun s => by positivity) ?_
            exact LE.le.eventuallyLE
              (fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 ht.2⟩)
      _ = 2 * (∫ s in Set.Icc (0 : ℝ) T, ‖u.hiL2 s‖ * ‖u.lo.deriv s‖) := by
            rw [← MeasureTheory.integral_const_mul]
      _ ≤ 2 * (‖u.hiL2‖ * ‖u.lo.deriv‖) :=
            mul_le_mul_of_nonneg_left hholder (by positivity)
  have hsq' :
      ‖u.repr t‖ ^ 2 ≤ 4 * (1 + T) * ‖f‖ ^ 2 := by
    nlinarith [hsq, hcross, hmul]
  have hbase : 0 ≤ 1 + T := by linarith
  have hrhs : 0 ≤ 2 * Real.sqrt (1 + T) * ‖f‖ := by positivity
  refine (sq_le_sq₀ (norm_nonneg _) hrhs).1 ?_
  calc
    ‖u.repr t‖ ^ 2 ≤ 4 * (1 + T) * ‖f‖ ^ 2 := hsq'
    _ = (2 * Real.sqrt (1 + T) * ‖f‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hbase]
      ring

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
