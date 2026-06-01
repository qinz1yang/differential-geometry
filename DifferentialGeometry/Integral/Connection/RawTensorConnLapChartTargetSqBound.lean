import DifferentialGeometry.Integral.Connection.RawTensorConnLapNormSqChartPulledReprBound
import DifferentialGeometry.Integral.Measure.TensorChartPulled
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure
import DifferentialGeometry.Integral.L2.SmoothSections.Defs

/-!
# Chart-target form of the pointwise squared op-norm bound for
`rawTensorConnLap` by the chart-pulled representation data

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, and a smooth compactly supported `(r, s)`-tensor section `T`, this
file rewrites the pointwise squared op-norm bound

```
‖rawTensorConnLap g r s T.toSection b‖^2
    ≤ K * (‖tensorRSChartE_section_repr r s α T.toSection b‖^2
           + ‖fderiv ℝ (tensorRSChartE_section_repr r s α T.toSection ∘
                (extChartAt I α).symm) (extChartAt I α b)‖^2
           + ‖iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr r s α
                T.toSection ∘ (extChartAt I α).symm) (extChartAt I α b)‖^2)
```

into a form parametrised by a point `y : EuclN` of the chart-target image of
the intersection of the chart-`α` partition-of-unity tsupport with the
chart-`α` Levi-Civita good set, with the LHS expressed via
`tensorTrivProjPushedNormSq` and the RHS expressed in terms of the inverse
chart applied to `toEuclidean.symm y`.

The constant `K` depends on `g`, the chart at `α`, the chart-atlas locality
hypotheses, and the ranks `r`, `s`; it is independent of `T` and `y`.

## Strategy

1. Extract `K` from the chart-pulled representation squared bound
   (`rawTensorConnLap_norm_sq_le_chartPulledRepr_data_on_pou_tsupport_goodSet`).
2. Given `y` in the `toEuclidean`-image of the `extChartAt`-image of the
   intersection `POU ∩ goodSet`, unpack a witness `b ∈ POU ∩ goodSet` with
   `y = toEuclidean (extChartAt I α b)`.
3. Rewrite the LHS via `tensorTrivProjPushedNormSq_apply_of_mem` (the point
   `y` lies inside `chartTargetEuclid α` by
   `chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid`).
4. Substitute `(extChartAt I α).symm ((toEuclidean (E := E)).symm y) = b`
   and use the fact that `‖TensorRSSpace.toModel T‖` agrees with `‖T‖` (by
   construction of the induced norm on the fibre).
5. Conclude using the source bound at `b`, substituting the chart-target
   identifications on the RHS.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

end Connection
end Integral
end DifferentialGeometry

end
