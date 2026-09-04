import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Projection.TimeL2EigenProjection
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Space

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

open scoped Classical in
omit [BoundarylessManifold I M] in
theorem spatialProj_coeff (σ : ℝ) (N : ℕ)
    (W : TensorHs (I := I) (M := M) g 0 2 σ)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    (spatialEigenProj (I := I) (M := M) g σ N W).coeff i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then W.coeff i else 0 := by
  rw [spatialEigenProj_apply, finiteEigenComboHs_coeff]

open scoped Classical in
omit [BoundarylessManifold I M] in
theorem spatialProj_idem (σ : ℝ) (N : ℕ)
    (W : TensorHs (I := I) (M := M) g 0 2 σ) :
    spatialEigenProj (I := I) (M := M) g σ N
        (spatialEigenProj (I := I) (M := M) g σ N W) =
      spatialEigenProj (I := I) (M := M) g σ N W := by
  classical
  refine TensorHs.ext (funext fun i => ?_)
  simp only [spatialProj_coeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N <;> simp [hi]

omit [BoundarylessManifold I M] in
theorem spatialProj_lip (σ : ℝ) (N : ℕ) :
    LipschitzWith 1 (spatialEigenProj (I := I) (M := M) g σ N) := by
  refine LipschitzWith.of_dist_le_mul (fun W W' => ?_)
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact norm_spatialEigenProj_apply_le (I := I) (M := M) g σ N (W - W')

open scoped Classical in
omit [BoundarylessManifold I M] in
theorem timeProj_modeCoeff (σ T : ℝ) (N : ℕ)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 σ) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    timeModeCoeff (I := I) (M := M)
        (timeL2EigenProj (I := I) (M := M) g σ T N f) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        timeModeCoeff (I := I) (M := M) f i else 0 := by
  classical
  have hL := timeModeCoeff_coeFn (I := I) (M := M)
    (timeL2EigenProj (I := I) (M := M) g σ T N f) i
  have hP : ⇑(timeL2EigenProj (I := I) (M := M) g σ T N f) =ᵐ[timeMeasure T]
      fun t => spatialEigenProj (I := I) (M := M) g σ N (f t) :=
    ContinuousLinearMap.coeFn_compLpL _ f
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, hP, timeModeCoeff_coeFn (I := I) (M := M) f i]
      with t h1 h2 h3
    rw [h1, h2, spatialProj_coeff, if_pos hi, h3]
  · rw [if_neg hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, hP, MeasureTheory.Lp.coeFn_zero ℝ 2 (timeMeasure T)]
      with t h1 h2 h3
    rw [h1, h2, spatialProj_coeff, if_neg hi, h3, Pi.zero_apply]

open scoped Classical in
omit [BoundarylessManifold I M] in
theorem proj_solutionModeCoeff {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    solutionModeCoeff (I := I) (M := M) (a := a) hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        solutionModeCoeff (I := I) (M := M) (a := a) hT f i else 0 := by
  classical
  rw [solutionModeCoeff, timeProj_modeCoeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi, if_pos hi, solutionModeCoeff]
  · rw [if_neg hi, if_neg hi, map_zero]

open scoped Classical in
omit [BoundarylessManifold I M] in
theorem proj_derivModeCoeff {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    derivModeCoeff (I := I) (M := M) (a := a) hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        derivModeCoeff (I := I) (M := M) (a := a) hT f i else 0 := by
  classical
  rw [derivModeCoeff, timeProj_modeCoeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi, if_pos hi, derivModeCoeff]
  · rw [if_neg hi, if_neg hi, map_zero]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma homModeCoeFn {a T : ℝ}
    (u₀ : TensorHs (I := I) (M := M) g 0 2 (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ⇑(homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) =ᵐ[timeMeasure T]
      fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        u₀.coeff i :=
  coeFn_ofContinuousOn _

open scoped Classical in
omit [BoundarylessManifold I M] in
theorem proj_homModeCoeff {a T : ℝ} (N : ℕ)
    (u₀ : TensorHs (I := I) (M := M) g 0 2 (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    homModeCoeff (I := I) (M := M) (a := a) (T := T)
        (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i else 0 := by
  classical
  have hL := homModeCoeFn (I := I) (M := M) (a := a) (T := T) g
    (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) i
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, homModeCoeFn (I := I) (M := M) (a := a) (T := T) g u₀ i]
      with t h1 h2
    rw [h1, h2, spatialProj_coeff, if_pos hi]
  · rw [if_neg hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, MeasureTheory.Lp.coeFn_zero ℝ 2 (timeMeasure T)]
      with t h1 h2
    rw [h1, h2, spatialProj_coeff, if_neg hi, mul_zero, Pi.zero_apply]

omit [BoundarylessManifold I M] in
theorem proj_solutionField_comm {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    maximalRegularitySolutionField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularitySolutionField (I := I) (M := M) a hT f) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact (timeL2EigenProj (I := I) (M := M) g a T N f) i,
    proj_solutionModeCoeff (I := I) (M := M) g hT N f i,
    timeProj_modeCoeff (I := I) (M := M) g (a + 2) T N
      (maximalRegularitySolutionField (I := I) (M := M) a hT f) i,
    maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact f i]

omit [BoundarylessManifold I M] in
theorem proj_derivField_comm {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    maximalRegularityDerivField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g a T N
        (maximalRegularityDerivField (I := I) (M := M) a hT f) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact (timeL2EigenProj (I := I) (M := M) g a T N f) i,
    proj_derivModeCoeff (I := I) (M := M) g hT N f i,
    timeProj_modeCoeff (I := I) (M := M) g a T N
      (maximalRegularityDerivField (I := I) (M := M) a hT f) i,
    maximalRegularityDerivField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact f i]

omit [BoundarylessManifold I M] in
theorem proj_homField_comm {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (u₀ : TensorHs (I := I) (M := M) g 0 2 (a + 2)) :
    maximalRegularityHomogeneousSolutionField (I := I) (M := M) a T
        (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularityHomogeneousSolutionField (I := I) (M := M) a T u₀) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maximalRegularityHomogeneousSolutionField_timeModeCoeff (I := I) (M := M) (a := a) (T := T)
      hT (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) i,
    proj_homModeCoeff (I := I) (M := M) g N u₀ i,
    timeProj_modeCoeff (I := I) (M := M) g (a + 2) T N
      (maximalRegularityHomogeneousSolutionField (I := I) (M := M) a T u₀) i,
    maximalRegularityHomogeneousSolutionField_timeModeCoeff (I := I) (M := M) (a := a) (T := T)
      hT u₀ i]

omit [BoundarylessManifold I M] in
theorem proj_duhamel_comm {a T : ℝ} (hT : 0 < T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (u₀ : TensorHs (I := I) (M := M) g 0 2 (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT
        (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀)
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ f) := by
  rw [maximalRegularityDuhamelSolutionField, maximalRegularityDuhamelSolutionField, map_add,
    proj_homField_comm (I := I) (M := M) g hT.le N h_compact u₀,
    proj_solutionField_comm (I := I) (M := M) g hT.le N h_compact f]

omit [BoundarylessManifold I M] in
theorem projDuhamel_zero {a T : ℝ} (hT : 0 < T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT
        (0 : TensorHs (I := I) (M := M) g 0 2 (a + 2))
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT
          (0 : TensorHs (I := I) (M := M) g 0 2 (a + 2)) f) := by
  have h := proj_duhamel_comm (I := I) (M := M) g hT N h_compact
    (0 : TensorHs (I := I) (M := M) g 0 2 (a + 2)) f
  rwa [map_zero] at h

omit [BoundarylessManifold I M] in
theorem proj_maximalRegularityOp_deriv {a T : ℝ} (hT : 0 < T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    timeH1.timeDeriv _ T
        (maximalRegularityOp (I := I) (M := M) a hT
          (timeL2EigenProj (I := I) (M := M) g a T N f)) =
      timeL2EigenProj (I := I) (M := M) g a T N
        (timeH1.timeDeriv _ T
          (maximalRegularityOp (I := I) (M := M) a hT f)) := by
  rw [maximalRegularityOp_timeDeriv, maximalRegularityOp_timeDeriv,
    proj_derivField_comm (I := I) (M := M) g hT.le N h_compact f]

omit [BoundarylessManifold I M] in
theorem projSolution_mode_zero {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T)
    {i : TensorEigenIdx (I := I) (M := M) g 0 2}
    (hi : i ∉ eigenIdxFinset (I := I) (M := M) g N) :
    timeModeCoeff (I := I) (M := M)
      (maximalRegularitySolutionField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f)) i = 0 := by
  rw [maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact (timeL2EigenProj (I := I) (M := M) g a T N f) i,
    proj_solutionModeCoeff (I := I) (M := M) g hT N f i, if_neg hi]

omit [BoundarylessManifold I M] in
theorem projSolution_fixed {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 a) T) :
    timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularitySolutionField (I := I) (M := M) a hT
          (timeL2EigenProj (I := I) (M := M) g a T N f)) =
      maximalRegularitySolutionField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [timeProj_modeCoeff (I := I) (M := M) g (a + 2) T N
      (maximalRegularitySolutionField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f)) i]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi]
  · rw [if_neg hi,
      projSolution_mode_zero (I := I) (M := M) g hT N h_compact f hi]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
