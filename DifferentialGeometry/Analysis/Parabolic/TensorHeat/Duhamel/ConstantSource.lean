import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.Constant
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Affine

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def constantHeatResponse (g : SmoothRiemannianMetric I M) (m T c : ℝ) :
    timeH1 (TensorHs g 0 0 m) T :=
  timeH1.mk 0 (TimeSobolev.const T
    (ccTensorToHs g 0 m (scalarCc g ⟨fun _ => c, contMDiff_const⟩)))

def constantHeatResponseField (g : SmoothRiemannianMetric I M) (m T c : ℝ) :
    timeL2 (TensorHs g 0 0 (m + 2)) T :=
  (constantHeatResponse g (m + 2) T c).toFunL2

theorem constantHeatResponse_toFun (g : SmoothRiemannianMetric I M)
    (m T c : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (constantHeatResponse g m T c).toFun t =
      t • ccTensorToHs g 0 m (scalarCc g ⟨fun _ => c, contMDiff_const⟩) := by
  rw [constantHeatResponse, timeH1.toFun_mk_const _ _ ht, zero_add]

theorem constantHeatResponse_trace0 (g : SmoothRiemannianMetric I M) (m T c : ℝ) :
    timeH1.trace0 _ T (constantHeatResponse g m T c) = 0 := rfl

theorem constantHeatResponse_timeDeriv (g : SmoothRiemannianMetric I M) (m T c : ℝ) :
    timeH1.timeDeriv _ T (constantHeatResponse g m T c) =
      TimeSobolev.const T
        (ccTensorToHs g 0 m (scalarCc g ⟨fun _ => c, contMDiff_const⟩)) := rfl

theorem constantHeatResponseField_inclusion
    (g : SmoothRiemannianMetric I M) (m T c : ℝ) :
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show m ≤ m + 2 by linarith)).compLpL 2 (timeMeasure T)
        (constantHeatResponseField g m T c) =
      timeH1.toTimeL2 _ T (constantHeatResponse g m T c) := by
  rw [constantHeatResponseField, constantHeatResponse,
    timeH1.compLpL_toFunL2_mk_const, map_zero, tensorHsInclusion_ccTensorToHs]
  rfl

theorem constantHeatResponseField_laplacian
    (g : SmoothRiemannianMetric I M) (m T c : ℝ) :
    timeScaleLaplacian m (constantHeatResponseField g m T c) = 0 := by
  rw [timeScaleLaplacian,constantHeatResponseField, constantHeatResponse,
    timeH1.compLpL_toFunL2_mk_const, map_zero,
    tensorScaleLaplacian_ccTensorToHs_scalarCc_const, TimeSobolev.const_zero]
  change timeH1.toTimeL2 _ T (0 : timeH1 (TensorHs g 0 0 m) T) = 0
  exact map_zero _

theorem constantHeatResponse_equation
    (g : SmoothRiemannianMetric I M) (m T c : ℝ) :
    timeH1.timeDeriv _ T (constantHeatResponse g m T c) =
      timeScaleLaplacian m (constantHeatResponseField g m T c) +
      TimeSobolev.const T
        (ccTensorToHs g 0 m (scalarCc g ⟨fun _ => c, contMDiff_const⟩)) := by
  rw [constantHeatResponseField_laplacian, zero_add, constantHeatResponse_timeDeriv]

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
end
