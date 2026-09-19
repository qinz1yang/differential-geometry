import DifferentialGeometry.Geometry.Connection.LeviCivita.DifferenceNorm
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
  (chartBasisVecFiber chartGramMatrix chartGramMatrix_apply)
open scoped Manifold Topology ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M]
  [CompactSpace M] [I.Boundaryless] in
private theorem inner_sum_left (g : SmoothRiemannianMetric I M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) (w : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (u : TangentSpace I x) :
    g.inner x (∑ m, c m • w m) u = ∑ m, c m * g.inner x (w m) u := by
  classical
  rw [map_sum, sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem connChartComp (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (K : Fin 3 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    connectionDifferenceLowAt (I := I) g₁ g₂ x
        (fun a : Fin 3 => chartBasisVecFiber (I := I) α (K a) x) =
      ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ α (K 0) (K 1) m (extChartAt I α x) -
            chartChristoffel (I := I) g₂ α (K 0) (K 1) m (extChartAt I α x)) *
          chartGramMatrix (I := I) g₁ α x m (K 2) := by
  classical
  have hd := IsCovariantDerivativeOn.difference_apply
    (hcov := (metricCov (I := I) g₁).isCovariantDerivativeOnUniv)
    (hcov' := (metricCov (I := I) g₂).isCovariantDerivativeOnUniv)
    (σ := fun b : M => chartBasisVecFiber (I := I) α (K 1) b) (x := x) (hx := by trivial)
    (chartBasisVec_alpha_mdifferentiableAt (I := I) α (K 1) hx)
  have hd' :
      CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
          (chartBasisVecFiber (I := I) α (K 1) x)
          (chartBasisVecFiber (I := I) α (K 0) x) =
        (metricCov (I := I) g₁) (fun b : M => chartBasisVecFiber (I := I) α (K 1) b) x
            (chartBasisVecFiber (I := I) α (K 0) x) -
            (metricCov (I := I) g₂) (fun b : M => chartBasisVecFiber (I := I) α (K 1) b) x
            (chartBasisVecFiber (I := I) α (K 0) x) := by
    unfold CovariantDerivative.difference
    exact congrArg
      (fun L : TangentSpace I x →L[ℝ] TangentSpace I x =>
        L (chartBasisVecFiber (I := I) α (K 0) x)) hd
  have hLC₁ : metricCov (I := I) g₁ = LeviCivita (I := I) g₁ := rfl
  have hLC₂ : metricCov (I := I) g₂ = LeviCivita (I := I) g₂ := rfl
  change Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g₁ g₂ x)
      (fun a : Fin 3 => chartBasisVecFiber (I := I) α (K a) x) = _
  rw [connectionDifferenceLowAt_apply]
  rw [hd', hLC₁, hLC₂,
    LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g₁ α (K 0) (K 1) hx,
    LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g₂ α (K 0) (K 1) hx,
    ← Finset.sum_sub_distrib]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ α (K 0) (K 1) m (extChartAt I α x) •
            chartBasisVecFiber (I := I) α m x -
          chartChristoffel (I := I) g₂ α (K 0) (K 1) m (extChartAt I α x) •
            chartBasisVecFiber (I := I) α m x)) =
      ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g₁ α (K 0) (K 1) m (extChartAt I α x) -
            chartChristoffel (I := I) g₂ α (K 0) (K 1) m (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α m x from
    Finset.sum_congr rfl fun m _ => (sub_smul _ _ _).symm]
  rw [inner_sum_left]
  exact Finset.sum_congr rfl fun m _ => by rw [chartGramMatrix_apply]

end DifferentialGeometry.PDE.RicciFlow
