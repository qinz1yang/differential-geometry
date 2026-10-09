import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Metric
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- Raw covariant iteration agrees with bundled iteration on a smooth tensor. -/
theorem iteratedMetricCovariantDerivative_eq_iterCov
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) s) (k : ℕ) (x : M) :
    iteratedMetricCovariantDerivative g s (fun y => A y) k x =
      iterCov g s A k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    change metricCovariantDerivative g (s + k)
      (iteratedMetricCovariantDerivative g s (fun y => A y) k) x = _
    have heq : iteratedMetricCovariantDerivative g s (fun y => A y) k =
        fun y => iterCov g s A k y := by
      funext y
      exact ih y
    rw [heq]
    rfl

end DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The metric difference norm uses the same covariant iteration as the raw
tensor norm, including the conversion between the two slot arities. -/
theorem metricDerivNorm_eq_iteratedMetricCovariantDerivative
    (g h G : SmoothRiemannianMetric I M) (k : ℕ) (x : M) :
    metricDerivNorm k g h G x =
      tensor0SFiberNorm G x (2 + k)
        (iteratedMetricCovariantDerivative G 2
          (fun y => metricTensorField g y - metricTensorField h y) k x) := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis G x
  have hinv : MetricInverseInBasis G x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h' := metricInverseInBasis_of_orthonormal G basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  rw [metricDerivNorm_eq_iterCov g h G k basis hinv]
  change _ = tensor0SFiberNorm G x (2 + k)
    (iteratedMetricCovariantDerivative G 2
      (fun y => (metricTensorField g - metricTensorField h) y) k x)
  rw [iteratedMetricCovariantDerivative_eq_iterCov]
  rfl

/-- The same identity for the raw tensor obtained by currying the difference
of the original metric inner products. -/
theorem metricDerivNorm_eq_iterated_inner_difference
    (g h G : SmoothRiemannianMetric I M) (k : ℕ) (x : M) :
    metricDerivNorm k g h G x =
      tensor0SFiberNorm G x (2 + k)
        (iteratedMetricCovariantDerivative G 2
          (fun y => ((continuousMultilinearCurryFin1 ℝ (TangentSpace I y) ℝ).symm.toContinuousLinearMap.comp
            (g.inner y - h.inner y)).uncurryLeft) k x) := by
  have herror :
      (fun y => ((continuousMultilinearCurryFin1 ℝ (TangentSpace I y) ℝ).symm.toContinuousLinearMap.comp
        (g.inner y - h.inner y)).uncurryLeft) =
        (fun y => metricTensorField g y - metricTensorField h y) := by
    funext y
    ext v
    change g.inner y (v 0) (v 1) - h.inner y (v 0) (v 1) =
      metricTensorField g y v - metricTensorField h y v
    rw [metricTensorField_apply, metricTensorField_apply]
  rw [herror]
  exact metricDerivNorm_eq_iteratedMetricCovariantDerivative g h G k x

end DifferentialGeometry.CheegerGromovCompactness
