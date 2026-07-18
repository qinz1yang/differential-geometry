import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Scaling

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false




namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem metricTracePair0SAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {x : M}
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) (scaleMetric (I := I) c hc g) B =
      c⁻¹ * metricTracePair0SAt (I := I) g B := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) Real
      (TangentSpace I x) := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component (I := I) g x k l
        (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  have hinvScale :
      MetricInverseInBasis_gen (I := I) (scaleMetric (I := I) c hc g) x basis
        (fun i j => c⁻¹ * gInv i j) :=
    metricInvBasis_scale (I := I) c hc g basis gInv hinv
  rw [metricTracePair0SAt_eq_sum_basis (I := I)
      (scaleMetric (I := I) c hc g) basis (fun i j => c⁻¹ * gInv i j) hinvScale,
    metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring


theorem metricTraceFirstTwo0SAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) (scaleMetric (I := I) c hc g) T tail =
      c⁻¹ * metricTraceFirstTwo0SAt (I := I) g T tail := by
  unfold metricTraceFirstTwo0SAt
  exact metricTracePair0SAt_scaleMetric (I := I) c hc g
    (freezeFirstTwo0S (I := I) T tail)


theorem roughLap0STensor_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    roughLap0STensor (I := I) (scaleMetric (I := I) c hc g) nabla2A tail =
      c⁻¹ * roughLap0STensor (I := I) g nabla2A tail := by
  rw [roughLap0STensor_apply, roughLap0STensor_apply]
  exact metricTraceFirstTwo0SAt_scaleMetric (I := I) c hc g nabla2A tail

end

end DifferentialGeometry.Integral.Connection
