import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def zeroStateDeTurckRemainderH2 (g₀ g_bg : SmoothRiemannianMetric I M) :
    TensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ) :=
  ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
    (deTurckSmoothRemainder (I := I) g₀ g_bg
      (0 : SmoothCcTensor g₀ 0 2) (by norm_num)
      (gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g₀))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
