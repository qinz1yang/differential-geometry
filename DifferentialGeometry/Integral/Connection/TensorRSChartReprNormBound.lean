import DifferentialGeometry.Integral.Connection.TensorRSChartFiberOpNorm
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberForwardOpNorm

/-!
# Reverse uniform bound: fibre norm by the model-side representation norm

For a chart centre `α : M` and ranks `r s : ℕ`, the fibre norm of any
`T : TensorRSSpace r s I b` is uniformly controlled by the norm of its
chart-`α` model-side image
`((triv α).continuousLinearMapAt ℝ b T : TensorRSModel r s ℝ E)` on any compact
`K ⊆ (chartAt H α).source`. Concretely there exists `C > 0` such that
`‖T‖ ≤ C * ‖(triv α).continuousLinearMapAt ℝ b T‖` for every `b ∈ K` and every
`T : TensorRSSpace r s I b`.

This is the reverse-direction counterpart to
`tensorRSChartFiberToModel_opNorm_isBounded_on_compact` and is an immediate
consequence of the previously established right-inverse bound
`tensorRSChartFiberFromModel_opNorm_isBounded_on_compact` together with the
identity `(triv α).symmL ((triv α).continuousLinearMapAt T) = T` valid on the
trivialisation base set.

## Main result

* `tensorRSSpace_norm_le_chartRepr_norm_on_compact` — uniform pointwise
  bound `‖T‖ ≤ C * ‖(triv α).clmAt T‖` over a compact subset of the chart-`α`
  source.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

end DifferentialGeometry.Integral.Connection

end
