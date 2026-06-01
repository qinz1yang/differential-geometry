import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.Inclusion
import Mathlib.Analysis.Normed.Operator.Compact

/-!
# Rellich-type compactness for the intrinsic Sobolev tower

Compactness of the continuous linear inclusions `H^{k+1} ↪ H^k` of intrinsic
Sobolev Hilbert spaces of tensor fields on a closed Riemannian manifold.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Rellich-type compactness for the intrinsic Sobolev tower: the
continuous linear inclusion `H^{k+1} ↪ H^k` of intrinsic Sobolev Hilbert
spaces of `(r, s)`-tensor fields on a closed Riemannian manifold is a
compact operator for every `k`.

# Structural blocker

The proof requires a quantitative chart-side compactness step
(Rellich-Kondrachov on bounded subsets of `EuclideanSpace ℝ (Fin n)`
with smooth-cutoff truncation) combined with two-sided norm equivalence
between the partition-of-unity-weighted chart-Sobolev tower (the
on-disk Hilbert-Schmidt norm `tensorPouSobolevHsNorm g k T`) and an
intrinsic Sobolev tower. The latter equivalence is precisely the
content of
`DifferentialGeometry.PDE.RicciFlow.HebeyBlock.pou_weighted_norm_equals_chart_component_norm_up_to_constant`,
which is itself an outstanding obligation. Until that two-sided
equivalence is in place, the compactness step cannot be transferred
along the natural completion map, so the body of this theorem remains
open. -/
theorem tensorPouSobolevHilbert_inclusion_isCompactOperator
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    IsCompactOperator (inclusionHk_succ (I := I) (M := M) g r s k) := by
  sorry

/-- Compactness of the depth-1 intrinsic Sobolev inclusion
`H^1 ↪ H^0 = L^2` for `(r, s)`-tensor fields on a closed Riemannian
manifold. The `k = 0` instance of
`tensorPouSobolevHilbert_inclusion_isCompactOperator`. -/
theorem TensorPouSobolevHilbert_inclusion_H2_L2_isCompact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (inclusionHk_succ (I := I) (M := M) g r s 0) :=
  tensorPouSobolevHilbert_inclusion_isCompactOperator
    (I := I) (M := M) g r s 0

end IntrinsicSobolev
end RicciFlow
end PDE
end DifferentialGeometry

end
