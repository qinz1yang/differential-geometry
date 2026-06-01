import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.PDE.DeTurck.Transformation
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Chart-component witnesses for an abstract metric operator

Type-level scaffolding for the chart-component smoothness and chart-component
symmetry of an abstract operator `F` on smooth Riemannian metrics, in the shape
consumed by the Phase 7/8 quasi-linear short-time existence pipeline.
-/

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open Bundle MeasureTheory
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Chart-component smoothness witness for an abstract metric operator `F`
under the hypothesis that `F` has smooth quasi-linear dependence on metric data:
for every metric `g`, basepoint `α`, and pair of model-basis indices `(i, j)`,
the scalar function
`x ↦ F g x (e_i^α(x)) (e_j^α(x))`
with `e_i^α(x) := (trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)`
is `C^∞` on the chart source at `α`.

This is a projection from the first conjunct of `IsSmoothQuasilinearMetricRHS`.
The chart-`α`-pushforward frame vectors form a smooth local frame for
`TangentSpace I` over the chart-`α` source — the natural smooth analogue of
the constant model basis on a non-parallelizable manifold. -/
theorem F_canonical_chart_component_smooth
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hF : DifferentialGeometry.PDE.IsSmoothQuasilinearMetricRHS (I := I) F)
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => F g x
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E i))
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E j)))
      (chartAt H α).source :=
  hF.1 g α i j

/-- Chart-component symmetry witness for an abstract metric operator `F`
under the hypothesis that `F`'s output is symmetric in its two tangent-vector
arguments: at every basepoint `x` (in particular `x ∈ (chartAt H α).source`),
the chart-`α`-pushforward frame components
`F g x (e_i^α(x)) (e_j^α(x))` are symmetric in the pair of model-basis indices
`(i, j)`. -/
theorem F_chart_component_symmetric
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hSymm : ∀ (g : SmoothRiemannianMetric I M) (x : M)
      (v w : TangentSpace I x), F g x v w = F g x w v)
    (g : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    F g x
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E i))
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E j)) =
      F g x
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E j))
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x
          (chartModelBasis E i)) :=
  hSymm g x
    ((trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i))
    ((trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E j))

end RicciFlow
end PDE
end DifferentialGeometry
