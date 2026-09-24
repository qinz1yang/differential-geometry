import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.Forcing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.Estimates

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

private theorem solution_field_smul (hT : 0 ≤ T) (c : ℝ)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolutionField a hT (c • f) =
      c • maximalRegularitySolutionField a hT f := by
  have hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
  refine timeModeCoeff_injective (I := I) (M := M) hc (fun i => ?_)
  rw [maximalRegularitySolutionField_timeModeCoeff (h_compact := hc),
    timeModeCoeff_smul, maximalRegularitySolutionField_timeModeCoeff (h_compact := hc)]
  rw [solutionModeCoeff, solutionModeCoeff, timeModeCoeff_smul, map_smul]

def maximalRegularitySolutionFieldL (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    timeL2 (TensorHs (I := I) (M := M) g r s a) T →L[ℝ]
      timeL2 (TensorHs (I := I) (M := M) g r s (a + 2)) T :=
  LinearMap.mkContinuous
    { toFun := maximalRegularitySolutionField a hT
      map_add' := maximalRegularitySolutionField_add hT
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
      map_smul' := solution_field_smul hT }
    (1 + T) (maximalRegularitySolutionField_norm_le
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) hT)

@[simp] theorem maximalRegularitySolutionFieldL_apply (hT : 0 ≤ T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolutionFieldL a hT f = maximalRegularitySolutionField a hT f :=
  rfl

theorem maximalRegularitySolutionFieldL_norm_le (hT : 0 ≤ T) :
    ‖maximalRegularitySolutionFieldL (I := I) (M := M) (g := g) (r := r) (s := s) a hT‖ ≤
      1 + T := by
  exact LinearMap.mkContinuous_norm_le _ (by linarith) _

theorem maximalRegularitySolutionFieldL_eq_duhamel (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    maximalRegularitySolutionFieldL a hT.le f =
      maximalRegularityDuhamelSolutionField a hT 0 f := by
  have hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
  have hzero := maximalRegularityHomogeneousSolutionField_norm_le
    (I := I) (M := M) (h_compact := hc) (a := a)
    (0 : TensorHs (I := I) (M := M) g r s (a + 2)) hT.le
  simp only [norm_zero, mul_zero] at hzero
  rw [maximalRegularitySolutionFieldL_apply, maximalRegularityDuhamelSolutionField,
    norm_le_zero_iff.mp hzero, zero_add]

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
