import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.FieldIdentification
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Interpolation.TimeL2Limit
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTraceContinuity
import DifferentialGeometry.Analysis.ODE.LinearIntegralEquation
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.StrongBackwardIdentification
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.SmallTime

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

private theorem norm_homModeCoeff_sq_eq
    (u₀ : TensorHs g r s (a + 2)) (i : TensorEigenIdx g r s) :
    ‖homModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 =
      ∫ t in Icc (0 : ℝ) T, Real.exp (-(2 * i.lambda) * t) * (u₀.coeff i) ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [TimeSobolev.coeFn_ofContinuousOn
    (Continuous.continuousOn (by fun_prop) :
      ContinuousOn (fun t : ℝ => Real.exp (-i.lambda * t) * u₀.coeff i) (Icc 0 T))]
    with t ht
  change ‖(TimeSobolev.ofContinuousOn (X := ℝ) (T := T)
    (f := fun t => Real.exp (-i.lambda * t) * u₀.coeff i)
    (Continuous.continuousOn (by fun_prop)) : timeL2 ℝ T) t‖ ^ 2 = _
  rw [ht, Real.norm_eq_abs, sq_abs, mul_pow, pow_two, ← Real.exp_add]
  congr 2
  ring

private theorem lambda_mul_norm_homModeCoeff_sq_le (hT : 0 ≤ T)
    (u₀ : TensorHs g r s (a + 2)) (i : TensorEigenIdx g r s) :
    i.lambda * ‖homModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 ≤
      (1 / 2 : ℝ) * (u₀.coeff i) ^ 2 := by
  rw [norm_homModeCoeff_sq_eq, ← MeasureTheory.integral_const_mul]
  have hconvert :
      (∫ t in Icc (0 : ℝ) T,
        i.lambda * (Real.exp (-(2 * i.lambda) * t) * (u₀.coeff i) ^ 2)) =
        (1 / 2 : ℝ) * (u₀.coeff i) ^ 2 *
          (∫ t in (0 : ℝ)..T, (2 * i.lambda) * Real.exp (-((2 * i.lambda) * (t - 0)))) := by
    rw [intervalIntegral.integral_of_le hT,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    ring_nf
  rw [hconvert]
  have hkernel := kernelIntegral_time_le_one (2 * i.lambda) 0 T
  have hfactor : 0 ≤ (1 / 2 : ℝ) * (u₀.coeff i) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith

private theorem tensorSobolevWeight_succ (i : TensorEigenIdx g r s) (b : ℝ) :
    tensorSobolevWeight i (b + 1) = tensorSobolevWeight i b * (1 + i.lambda) := by
  have hbase : (0 : ℝ) < 1 + i.lambda := by
    have h := tensor_lambda_nonneg i
    linarith
  rw [tensorSobolevWeight, tensorSobolevWeight, Real.rpow_add hbase, Real.rpow_one]

private theorem weighted_homModeCoeff_succ_le (hT : 0 ≤ T)
    (u₀ : TensorHs g r s (a + 2)) (i : TensorEigenIdx g r s) :
    tensorSobolevWeight i ((a + 2) + 1) *
        ‖homModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 ≤
      (T + 1 / 2) * (tensorSobolevWeight i (a + 2) * (u₀.coeff i) ^ 2) := by
  have htime := norm_homModeCoeff_sq_le hT u₀ i
  have heigen := lambda_mul_norm_homModeCoeff_sq_le hT u₀ i
  have hmode : (1 + i.lambda) * ‖homModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 ≤
      (T + 1 / 2) * (u₀.coeff i) ^ 2 := by nlinarith
  calc
    tensorSobolevWeight i ((a + 2) + 1) *
        ‖homModeCoeff (a := a) (T := T) u₀ i‖ ^ 2 =
      tensorSobolevWeight i (a + 2) *
        ((1 + i.lambda) * ‖homModeCoeff (a := a) (T := T) u₀ i‖ ^ 2) := by
      rw [tensorSobolevWeight_succ]
      ring
    _ ≤ tensorSobolevWeight i (a + 2) * ((T + 1 / 2) * (u₀.coeff i) ^ 2) :=
      mul_le_mul_of_nonneg_left hmode (tensorSobolevWeight_nonneg i (a + 2))
    _ = _ := by ring

private theorem summable_homModeCoeff_succ (hT : 0 ≤ T)
    (u₀ : TensorHs g r s (a + 2)) :
    Summable (fun i => tensorSobolevWeight i ((a + 2) + 1) *
      ‖homModeCoeff (a := a) (T := T) u₀ i‖ ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun i => mul_nonneg (tensorSobolevWeight_nonneg i _) (sq_nonneg _))
    (weighted_homModeCoeff_succ_le hT u₀) (u₀.weighted_summable.mul_left (T + 1 / 2))


private def homogeneousInitial (u₀ : TensorHs g r s (a + 1)) :
    TensorHs g r s ((a - 1) + 2) :=
  tensorHsInclusion (g := g) (r := r) (s := s) (by linarith) u₀

def heatEvolutionField (a T : ℝ) (u₀ : TensorHs g r s (a + 1)) :
    timeL2 (TensorHs g r s (a + 2)) T :=
  timeL2OfModes (σ := a + 2)
    (homModeCoeff (a := a - 1) (T := T) (homogeneousInitial u₀))

private theorem heatEvolutionField_timeModeCoeff (hT : 0 ≤ T)
    (u₀ : TensorHs g r s (a + 1)) (i : TensorEigenIdx g r s) :
    timeModeCoeff (heatEvolutionField a T u₀) i =
      homModeCoeff (a := a - 1) (T := T) (homogeneousInitial u₀) i := by
  apply timeL2OfModes_timeModeCoeff
  have h := summable_homModeCoeff_succ hT (homogeneousInitial u₀)
  simpa only [show ((a - 1) + 2) + 1 = a + 2 by ring] using h

def heatEvolution (a T : ℝ) (u₀ : TensorHs g r s (a + 1)) :
    timeH1 (TensorHs g r s a) T :=
  timeH1.mk (tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith) u₀)
    (timeScaleLaplacian a (heatEvolutionField a T u₀))

theorem heatEvolution_trace0 (u₀ : TensorHs g r s (a + 1)) :
    timeH1.trace0 _ T (heatEvolution a T u₀) =
      tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith) u₀ := rfl

theorem heatEvolution_timeDeriv (u₀ : TensorHs g r s (a + 1)) :
    timeH1.timeDeriv _ T (heatEvolution a T u₀) =
      timeScaleLaplacian a (heatEvolutionField a T u₀) := rfl

private theorem heatEvolution_deriv_coeff_ae (hT : 0 ≤ T)
    (u₀ : TensorHs g r s (a + 1)) (i : TensorEigenIdx g r s) :
    (fun t => ((heatEvolution a T u₀).deriv t).coeff i) =ᵐ[timeMeasure T]
      (homDerivModeCoeff (a := a - 1) (T := T) (homogeneousInitial u₀) i) := by
  have hm : timeModeCoeff (heatEvolution a T u₀).deriv i =
      homDerivModeCoeff (a := a - 1) (T := T) (homogeneousInitial u₀) i := by
    change timeModeCoeff (timeScaleLaplacian a (heatEvolutionField a T u₀)) i = _
    rw [timeModeCoeff_timeScaleLaplacian, heatEvolutionField_timeModeCoeff hT,
      homDerivModeCoeff_eq_smul]
  exact (timeModeCoeff_coeFn (heatEvolution a T u₀).deriv i).symm.trans
    (Filter.Eventually.of_forall fun t => congrArg (fun f : timeL2 ℝ T => f t) hm)

private theorem heatEvolution_coeff_ae (hT : 0 ≤ T)
    (u₀ : TensorHs g r s (a + 1)) (i : TensorEigenIdx g r s) :
    (fun t => (heatEvolutionField a T u₀ t).coeff i) =ᵐ[timeMeasure T]
      fun t => ((heatEvolution a T u₀).toFun t).coeff i := by
  have hmode := timeModeCoeff_coeFn (heatEvolutionField a T u₀) i
  rw [heatEvolutionField_timeModeCoeff hT] at hmode
  have hftc := homModeCoeff_eq_initial_add_integral (a := a - 1) (T := T)
    (homogeneousInitial u₀) i
  have hd := heatEvolution_deriv_coeff_ae hT u₀ i
  filter_upwards [hmode, hftc, ae_restrict_mem (μ := volume) measurableSet_Icc]
    with t ht hft htmem
  rw [← ht, hft]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hsub : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc h0 htmem)
  have hint : (∫ z in (0 : ℝ)..t,
      homDerivModeCoeff (a := a - 1) (T := T) (homogeneousInitial u₀) i z) =
      ∫ z in (0 : ℝ)..t, ((heatEvolution a T u₀).deriv z).coeff i := by
    refine intervalIntegral.integral_congr_ae ?_
    have hh := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hd
    rw [ae_restrict_iff' measurableSet_uIoc] at hh
    filter_upwards [hh] with z hz hzm
    exact (hz hzm).symm
  rw [hint]
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm
    (tensorHsCoeffL (g := g) (r := r) (s := s) (a := a) i)
    ((heatEvolution a T u₀).intervalIntegrable_deriv h0 htmem)
  change u₀.coeff i + _ =
    (tensorHsCoeffL (g := g) (r := r) (s := s) (a := a) i) ((heatEvolution a T u₀).toFun t)
  rw [timeH1.toFun_apply, map_add, ← hcomm]
  rfl

theorem heatEvolutionField_toTimeL2 (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) :
    timeL2Inclusion (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith)
      (heatEvolutionField a T u₀) = timeH1.toTimeL2 _ T (heatEvolution a T u₀) := by
  have : Countable (TensorEigenIdx g r s) := countable_tensorEigenIdx hc
  apply Lp.ext
  have hall := (ae_all_iff.mpr fun i => heatEvolution_coeff_ae hT u₀ i)
  have hinc := (tensorHsInclusion (g := g) (r := r) (s := s)
    (show a ≤ a + 2 by linarith)).coeFn_compLpL (p := 2) (μ := timeMeasure T)
      (heatEvolutionField a T u₀)
  have hrep := TimeSobolev.coeFn_ofContinuousOn (heatEvolution a T u₀).continuousOn_toFun
  filter_upwards [hall, hinc, hrep] with t ht hi hr
  calc
    _ = tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith)
        (heatEvolutionField a T u₀ t) := hi
    _ = (heatEvolution a T u₀).toFun t := by
      apply TensorHs.ext
      funext i
      exact ht i
    _ = _ := hr.symm


theorem heatEvolutionField_inclusion (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 2)) :
    heatEvolutionField a T
        (tensorHsInclusion (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith) u₀) =
      maximalRegularityHomogeneousSolutionField a T u₀ := by
  apply timeModeCoeff_injective hc
  intro i
  rw [heatEvolutionField_timeModeCoeff hT,
    maximalRegularityHomogeneousSolutionField_timeModeCoeff hT]
  rfl

theorem heatEvolution_inclusion (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 2)) :
    heatEvolution a T
        (tensorHsInclusion (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith) u₀) =
      maximalRegularityHomogeneous a T u₀ := by
  apply timeH1.ext
  · apply TensorHs.ext
    rfl
  · change timeScaleLaplacian a (heatEvolutionField a T _) =
      maximalRegularityHomogeneousDerivField a T u₀
    rw [heatEvolutionField_inclusion hT hc]
    exact (maximalRegularityHomogeneousDerivField_eq_scaleLaplacian hT hc u₀).symm

def heatDuhamelEvolutionField (a : ℝ) {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs g r s (a + 1)) (F : timeL2 (TensorHs g r s a) T) :
    timeL2 (TensorHs g r s (a + 2)) T :=
  heatEvolutionField a T u₀ + maximalRegularitySolutionField a hT.le F

def heatDuhamelEvolution (a : ℝ) {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs g r s (a + 1)) (F : timeL2 (TensorHs g r s a) T) :
    timeH1 (TensorHs g r s a) T :=
  heatEvolution a T u₀ + maximalRegularityOp a hT F

theorem heatDuhamelEvolution_trace0 (hT : 0 < T)
    (u₀ : TensorHs g r s (a + 1)) (F : timeL2 (TensorHs g r s a) T) :
    timeH1.trace0 _ T (heatDuhamelEvolution a hT u₀ F) =
      tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith) u₀ := by
  rw [heatDuhamelEvolution, map_add, heatEvolution_trace0,
    maximalRegularityOp_trace0 hT F, add_zero]

theorem heatDuhamelEvolution_timeDeriv (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) (F : timeL2 (TensorHs g r s a) T) :
    timeH1.timeDeriv _ T (heatDuhamelEvolution a hT u₀ F) =
      timeScaleLaplacian a (heatDuhamelEvolutionField a hT u₀ F) + F := by
  rw [heatDuhamelEvolution, map_add, heatEvolution_timeDeriv,
    maximalRegularityOp_solves hc hT F, heatDuhamelEvolutionField, map_add]
  abel

theorem heatDuhamelEvolutionField_inclusion (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 2)) (F : timeL2 (TensorHs g r s a) T) :
    heatDuhamelEvolutionField a hT
        (tensorHsInclusion (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith) u₀) F =
      maximalRegularityDuhamelSolutionField a hT u₀ F := by
  rw [heatDuhamelEvolutionField, heatEvolutionField_inclusion hT.le hc]
  rfl

theorem heatDuhamelEvolution_inclusion (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 2)) (F : timeL2 (TensorHs g r s a) T) :
    heatDuhamelEvolution a hT
        (tensorHsInclusion (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith) u₀) F =
      maximalRegularityDuhamelMap a hT u₀ F := by
  rw [heatDuhamelEvolution, heatEvolution_inclusion hT.le hc]
  rfl


private theorem homogeneous_solutionField_zero (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s)) :
    maximalRegularityHomogeneousSolutionField (g := g) (r := r) (s := s) a T 0 = 0 := by
  apply timeModeCoeff_injective hc
  intro i
  rw [maximalRegularityHomogeneousSolutionField_timeModeCoeff hT]
  change homModeCoeff (a := a) (T := T) (0 : TensorHs g r s (a + 2)) i = 0
  have hb := norm_homModeCoeff_sq_le hT (0 : TensorHs g r s (a + 2)) i
  simp only [TensorHs.zero_coeff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero] at hb
  apply norm_le_zero_iff.mp
  nlinarith [norm_nonneg (homModeCoeff (a := a) (T := T) (0 : TensorHs g r s (a + 2)) i)]

private theorem homogeneous_zero (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s)) :
    maximalRegularityHomogeneous (g := g) (r := r) (s := s) a T 0 = 0 := by
  apply timeH1.ext
  · change tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith) 0 = 0
    exact map_zero _
  · change maximalRegularityHomogeneousDerivField a T 0 = 0
    rw [maximalRegularityHomogeneousDerivField_eq_scaleLaplacian hT hc,
      homogeneous_solutionField_zero hT hc, map_zero]

private theorem solutionField_toTimeL2 (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (F : timeL2 (TensorHs g r s a) T) :
    timeL2Inclusion (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith)
      (maximalRegularitySolutionField a hT.le F) = timeH1.toTimeL2 _ T (maximalRegularityOp a hT F) := by
  have h := solutionField_toFun_ae hT hc (0 : TensorHs g r s (a + 2)) F
  rw [maximalRegularityDuhamelSolutionField, homogeneous_solutionField_zero hT.le hc,
    zero_add, maximalRegularityDuhamelMap, homogeneous_zero hT.le hc, zero_add] at h
  apply Lp.ext
  have hinc := (tensorHsInclusion (g := g) (r := r) (s := s)
    (show a ≤ a + 2 by linarith)).coeFn_compLpL (p := 2) (μ := timeMeasure T)
      (maximalRegularitySolutionField a hT.le F)
  have hrep := TimeSobolev.coeFn_ofContinuousOn (maximalRegularityOp a hT F).continuousOn_toFun
  filter_upwards [h, hinc, hrep] with t ht hi hr
  exact hi.trans (ht.trans hr.symm)

theorem heatDuhamelEvolutionField_toTimeL2 (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) (F : timeL2 (TensorHs g r s a) T) :
    timeL2Inclusion (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith)
      (heatDuhamelEvolutionField a hT u₀ F) =
      timeH1.toTimeL2 _ T (heatDuhamelEvolution a hT u₀ F) := by
  rw [heatDuhamelEvolutionField, heatDuhamelEvolution, map_add, map_add,
    heatEvolutionField_toTimeL2 hT.le hc, solutionField_toTimeL2 hT hc]

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

private theorem heatEvolution_link (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) :
    ∀ᵐ t ∂timeMeasure T, tensorHsInclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) (heatEvolutionField a T u₀ t) = (heatEvolution a T u₀).toFun t := by
  have hi := (tensorHsInclusion (g := g) (r := r) (s := s)
    (show a ≤ a + 2 by linarith)).coeFn_compLpL (p := 2) (μ := timeMeasure T)
    (heatEvolutionField a T u₀)
  have hr := TimeSobolev.coeFn_ofContinuousOn (heatEvolution a T u₀).continuousOn_toFun
  have hpin := heatEvolutionField_toTimeL2 hT hc u₀
  change (tensorHsInclusion (g := g) (r := r) (s := s)
    (show a ≤ a + 2 by linarith)).compLpL 2 (timeMeasure T)
    (heatEvolutionField a T u₀) = (heatEvolution a T u₀).toFunL2 at hpin
  filter_upwards [hi, hr] with t hit hrt
  rw [hpin] at hit
  exact hit.symm.trans hrt

def heatEvolutionCrossScale (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) : CrossScaleField g r s a T where
  highRegularity := heatEvolutionField a T u₀
  lowRegularity := heatEvolution a T u₀
  link := heatEvolution_link hT hc u₀

theorem heatEvolutionCrossScale_repr_initial (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) :
    (heatEvolutionCrossScale hT.le hc u₀).repr 0 = u₀ := by
  apply TensorHs.ext
  funext i
  rw [CrossScaleField.repr_coeff _ hT ⟨le_rfl, hT.le⟩]
  change ((heatEvolution a T u₀).toFun 0).coeff i = u₀.coeff i
  rw [timeH1.toFun_zero]
  rfl

theorem heatEvolutionCrossScale_repr_link (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith)
      ((heatEvolutionCrossScale hT.le hc u₀).repr t) = (heatEvolution a T u₀).toFun t := by
  apply TensorHs.ext
  funext i
  rw [tensorHsInclusion_coeff_apply, CrossScaleField.repr_coeff _ hT ht]
  rfl

theorem heatEvolutionCrossScale_repr_ae (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) :
    (heatEvolutionCrossScale hT.le hc u₀).repr =ᵐ[timeMeasure T]
      fun t => tensorHsInclusion (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (heatEvolutionField a T u₀ t) := by
  have hp := (heatEvolutionCrossScale hT.le hc u₀).ae_coeffFun_eq_hiL2
  filter_upwards [hp, ae_restrict_mem (μ := volume) measurableSet_Icc] with t hpt ht
  apply TensorHs.ext
  funext i
  rw [CrossScaleField.repr_coeff _ hT ht, tensorHsInclusion_coeff_apply]
  exact hpt i

theorem heatEvolutionCrossScale_repr_near_initial (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) δ,
      ‖(heatEvolutionCrossScale hT.le hc u₀).repr t - u₀‖ < ε := by
  let u := heatEvolutionCrossScale hT.le hc u₀
  have hc0 := u.continuousOn_repr 0 (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl, hT.le⟩)
  rw [Metric.continuousWithinAt_iff] at hc0
  obtain ⟨δ, hδ, hclose⟩ := hc0 ε hε
  refine ⟨min T (δ / 2), lt_min hT (half_pos hδ), min_le_left _ _, ?_⟩
  intro t ht
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have htd : dist t (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt (ht.2.trans (min_le_right _ _)) (by linarith)
  have hn := hclose htT htd
  rw [show u.repr 0 = u₀ from heatEvolutionCrossScale_repr_initial hT hc u₀, dist_eq_norm] at hn
  exact hn
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem strongPair_toFun_coeff
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    (i : TensorEigenIdx g r s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (u.toFun t).coeff i = Real.exp (-i.lambda * t) * u.initial.coeff i := by
  let x := strongCross U u hU
  apply DifferentialGeometry.Analysis.ODE.eq_exp_mul_of_integral_eq (ht.1.trans ht.2)
    (f := fun q => (u.toFun q).coeff i)
  · exact x.continuousOn_coeffFun i
  · intro z hz
    have hmode : ∀ᵐ q ∂timeMeasure T,
        (u.deriv q).coeff i = -i.lambda * x.coeffFun i q := by
      have hDelta := timeScaleLaplacian_coeFn U
      filter_upwards [hDelta, x.ae_coeffFun_eq_hiL2] with q hq hx
      rw [show u.deriv = timeScaleLaplacian a U from heq, hq, tensorScaleLaplacian_coeff, hx i]
      rfl
    have hsub : Ioc (0 : ℝ) z ⊆ Icc (0 : ℝ) T :=
      fun q hq => ⟨hq.1.le, hq.2.trans hz.2⟩
    have hint : (∫ q in (0 : ℝ)..z, (u.deriv q).coeff i) =
        ∫ q in (0 : ℝ)..z, -i.lambda * x.coeffFun i q := by
      rw [intervalIntegral.integral_of_le hz.1, intervalIntegral.integral_of_le hz.1]
      exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hmode)
    have h := x.coeffFun_eq_integral i hz
    change (u.toFun z).coeff i = u.initial.coeff i + ∫ q in (0 : ℝ)..z, (u.deriv q).coeff i at h
    rw [hint] at h
    exact h
  · exact ht

theorem heatEvolution_toFun_coeff (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) (i : TensorEigenIdx g r s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ((heatEvolution a T u₀).toFun t).coeff i = Real.exp (-i.lambda * t) * u₀.coeff i :=
  strongPair_toFun_coeff (heatEvolution a T u₀) (heatEvolutionField a T u₀)
    (heatEvolutionField_toTimeL2 hT hc u₀) (heatEvolution_timeDeriv u₀) i ht

theorem heatEvolution_toFun_eqOn {S : ℝ} (hS : 0 ≤ S) (hT : S ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) :
    EqOn (heatEvolution a S u₀).toFun (heatEvolution a T u₀).toFun (Icc (0 : ℝ) S) := by
  intro t ht
  apply TensorHs.ext
  funext i
  rw [heatEvolution_toFun_coeff hS hc u₀ i ht,
    heatEvolution_toFun_coeff (hS.trans hT) hc u₀ i ⟨ht.1, ht.2.trans hT⟩]

theorem heatEvolutionField_eq_ae {S : ℝ} (hS : 0 < S) (hST : S ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) :
    heatEvolutionField a S u₀ =ᵐ[timeMeasure S] heatEvolutionField a T u₀ := by
  have hT : 0 < T := hS.trans_le hST
  have hpS := (heatEvolutionCrossScale hS.le hc u₀).link
  have hpT := (heatEvolutionCrossScale hT.le hc u₀).link
  have hm : timeMeasure S ≤ timeMeasure T := Measure.restrict_mono (Icc_subset_Icc le_rfl hST) le_rfl
  have hpT' := hpT.filter_mono (ae_mono hm)
  filter_upwards [hpS, hpT', ae_restrict_mem (μ := volume) measurableSet_Icc] with t hs ht hmem
  apply tensorHsInclusion_injective (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith)
  exact hs.trans ((heatEvolution_toFun_eqOn hS.le hST hc u₀ hmem).trans ht.symm)

theorem heatEvolutionField_norm_sq_eq_integral {S : ℝ} (hS : 0 < S) (hST : S ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) :
    ‖heatEvolutionField a S u₀‖ ^ 2 =
      ∫ t in Icc (0 : ℝ) S, ‖heatEvolutionField a T u₀ t‖ ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral]
  exact integral_congr_ae ((heatEvolutionField_eq_ae hS hST hc u₀).fun_comp (fun x => ‖x‖ ^ 2))
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a : ℝ}

theorem heatEvolutionField_norm_small_time
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (a + 1)) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ δ ∈ Ioc (0 : ℝ) τ, ∀ T ∈ Ioc (0 : ℝ) δ, ‖heatEvolutionField a T u₀‖ < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := TimeSobolev.exists_pos_integral_norm_sq_lt hτ
    (heatEvolutionField a τ u₀) (sq_pos_of_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro T hT
  have hsq := hsmall T ⟨hT.1.le, hT.2⟩
  rw [← heatEvolutionField_norm_sq_eq_integral hT.1 (hT.2.trans hδ.2) hc u₀] at hsq
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
