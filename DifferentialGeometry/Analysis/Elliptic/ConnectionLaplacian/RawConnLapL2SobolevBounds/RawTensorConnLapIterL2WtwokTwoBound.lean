import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapL2WtwokTwoBound
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def rawTensorConnLapSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor g r s :=
  tensorConnLaplacian_of_contMDiff (I := I) g r s T
    (rawTensorConnLap_contMDiff (I := I) g r s (fun z : M => T.toSection z)
      T.toSection.contMDiff_toFun)

end NormedSpaceModel

section NormedSpaceModelLemmas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma rawTensorConnLapSmooth_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (x : M) :
    (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
      rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := by
  unfold rawTensorConnLapSmooth
  exact tensorConnLaplacian_of_contMDiff_toFun (I := I) g r s T _ x

noncomputable def rawTensorConnLapIter
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ℕ → SmoothCcTensor g r s → SmoothCcTensor g r s
  | 0,     T => T
  | k + 1, T => rawTensorConnLapSmooth (I := I) g r s
                  (rawTensorConnLapIter g r s k T)

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem rawTensorConnLapIter_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s 0 T = T := rfl

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem rawTensorConnLapIter_succ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s (k + 1) T =
      rawTensorConnLapSmooth (I := I) g r s
        (rawTensorConnLapIter (I := I) g r s k T) := rfl

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
lemma rawTensorConnLapIter_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s 1 T =
      rawTensorConnLapSmooth (I := I) g r s T := rfl

end NormedSpaceModelLemmas

end Elliptic
end Analysis
end DifferentialGeometry

end
