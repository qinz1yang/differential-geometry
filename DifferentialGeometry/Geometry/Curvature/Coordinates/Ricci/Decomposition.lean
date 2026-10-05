import DifferentialGeometry.Geometry.Curvature.Riemann.Ricci

namespace DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Set Matrix
open scoped Manifold Topology ContDiff BigOperators Matrix
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartRicciSecondOrderTerm (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g α i k j) y -
      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g α i j j) y)

def chartRicciFirstOrderTerm (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    ∑ m : Fin (Module.finrank ℝ E),
      (chartChristoffel (I := I) g α j m j y *
          chartChristoffel (I := I) g α i k m y -
        chartChristoffel (I := I) g α k m j y *
          chartChristoffel (I := I) g α i j m y)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartRicciTensor_eq_secondOrder_add_firstOrder
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciTensor (I := I) g α i k y =
      chartRicciSecondOrderTerm (I := I) g α i k y +
        chartRicciFirstOrderTerm (I := I) g α i k y := by
  classical
  rw [chartRicciTensor_def, chartRicciSecondOrderTerm, chartRicciFirstOrderTerm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [chartRiemannTensor_def]

end

end DifferentialGeometry.Geometry.Curvature
