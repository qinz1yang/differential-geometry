import DifferentialGeometry.Analysis.Laplacian.MetricExtension

/-!
# Chart-pulled inverse Gram matrix entry: smoothness on the Euclidean chart target

For a smooth Riemannian metric `g` on a closed manifold `M` and a chart center
`α : M`, the scalar map
`y ↦ chartInvGramMatrix g α ((extChartAt I α).symm ((toEuclidean E).symm y)) k l`
is smooth on the Euclidean chart target `chartTargetEuclid α`. This is the
pullback through the chart `α` (composed with the canonical linear isometry
`toEuclidean : E ≃ₗᵢ EuclideanSpace ℝ (Fin n)`) of the `(k, l)`-entry of the
chart-`α` inverse Gram matrix.

The map factors as the composition

```
EuclideanSpace ℝ (Fin n)
  --(toEuclidean.symm : EuclideanSpace ≃ E)-->
    (extChartAt I α).target ⊆ E
  --((extChartAt I α).symm : E → M)-->
    chart-`α` base set ⊆ M
  --(chartInvGramMatrix g α · k l : M → ℝ)-->
    ℝ.
```

The first two pieces give a smooth map from the open set `chartTargetEuclid α`
to `M` (`MetricExtension.contMDiffOn_chart_symm`); the last piece is smooth on
the chart base set by `chartInvGramMatrix_entry_contMDiffOn`. Composing yields
the desired `ContDiffOn ℝ ∞` statement on `chartTargetEuclid α`.

This headline is a thin re-packaging of
`MetricExtension.invGramOnEuclid_contDiffOn`, restated without the named
intermediate function so downstream tensor-regularity files can consume it as
an inline smoothness fact on the pulled-back inverse Gram matrix entry.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The pullback of the chart-`α` inverse Gram matrix `(k, l)`-entry through
`(extChartAt I α).symm ∘ (toEuclidean E).symm` is smooth on the Euclidean
chart target `chartTargetEuclid α`. -/
theorem chartInvGramMatrix_pullback_contDiffOn_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        chartInvGramMatrix (I := I) g α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  invGramOnEuclid_contDiffOn (I := I) g α k l

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
