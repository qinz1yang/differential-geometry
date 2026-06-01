import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CompactInclusion
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Rellich.Tensor

/-!
# Compactness of the L²-side tensor resolvent

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the L²-side
compactness of the variational tensor resolvent
`tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`
factorises as
`tensorResolventL2 g r s = TensorH1ComplToTensorL2 g r s ∘L
  tensorResolvent g r s`,
a composition of the H¹ → L² compactness with the bounded resolvent.

The predicate-free (compactness-of-`M`-based) statements live in
`PDE/RicciFlow/IntrinsicSpectral/CompactSAResolventIntrinsic.lean`
(`tensorResolventL2_isCompactOperator`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
