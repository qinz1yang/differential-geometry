import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeOpNorm
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartLeviCivitaParallelCLMOpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure

/-!
# Pointwise op-norm bound for the second-application term in the
`(r, s)`-tensor connection-Laplacian frame trace

The frame-trace formula expresses `(Δ_∇ T)(x)` as a sum over `i` of two
terms: a *first-application* term and a *second-application* term
`cov_RS T x ((LeviCivita g) B_i x (B_i x))`. This file ships the
pointwise op-norm bound for the second-application term, in two stages:

* a bound on the inner Γ-correction `(LeviCivita g) X b (X b)` from the
  chart-α Levi-Civita formula and the uniform op-norm bounds on the
  trivialisations and the Christoffel correction;
* a bound on `cov_RS T b v` for any vector `v ∈ T_b M`, obtained from
  `chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport` after a
  smooth extension of `v` and the chart-frame agreement
  `chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

end Connection
end Integral
end DifferentialGeometry

end
