import DifferentialGeometry.Geometry.Operator.Product
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.Euclidean

/-!
Physical continuous linear coordinates on the Euclidean factor have zero Hessian for
its actual product Riemannian metric, independently of the second factor's geometry.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem euclidean_coordinate_hessian (ℓ : E →L[ℝ] ℝ) (x : E) :
    hessFun (I := 𝓘(ℝ, E)) (euclideanMetric (E := E)) ℓ x = 0 := by
  apply Module.Basis.ext (centeredChartTangentBasis (I := 𝓘(ℝ, E)) x)
  intro i
  apply Module.Basis.ext (centeredChartTangentBasis (I := 𝓘(ℝ, E)) x)
  intro j
  rw [hessFun_basis_apply, chartHessianTensor_def, chartIteratedPartialDeriv_def]
  have heq : scalarOnE (I := 𝓘(ℝ, E)) x ℓ = ℓ := by
    funext y
    rw [scalarOnE_def, extChartAt_model_space_eq_id]
    rfl
  rw [heq]
  simp_rw [chartChristoffel_euclideanMetric]
  have hfirst : partialDeriv (E := E) j ℓ = fun y : E => ℓ (chartModelBasis E j) := by
    funext y
    unfold partialDeriv
    rw [ℓ.fderiv]
  rw [hfirst]
  simp [partialDeriv]
  rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

theorem hessFun_euclideanProduct_coordinate
    (h : SmoothRiemannianMetric J N) (ℓ : E →L[ℝ] ℝ) (x : E × N) :
    hessFun (I := (𝓘(ℝ, E)).prod J) ((euclideanMetric (E := E)).prod h)
      (fun p : E × N => ℓ p.1) x = 0 := by
  let f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ := ⟨ℓ, ℓ.contDiff.contMDiff⟩
  let k : C^∞⟮J, N; ℝ⟯ := ⟨fun y : N => 0, contMDiff_const⟩
  have hzero : hessFun (I := J) h (fun y : N => (0 : ℝ)) x.2 = 0 := by
    change hessFun (I := J) h (0 : N → ℝ) x.2 = 0
    have hh := congrFun (hessFun_smul h 0 (fun y : N => (1 : ℝ))) x.2
    simpa using hh
  ext u v
  have hh := hessFun_prod (euclideanMetric (E := E)) h f k x u v
  change hessFun ((euclideanMetric (E := E)).prod h)
      (fun p : E × N => ℓ p.1 + 0) x u v =
    hessFun (euclideanMetric (E := E)) ℓ x.1 u.1 v.1 +
      hessFun h (fun y : N => (0 : ℝ)) x.2 u.2 v.2 at hh
  simp only [add_zero] at hh
  rw [hh, euclidean_coordinate_hessian, hzero]
  change (0 : ℝ) + 0 = 0
  exact zero_add 0

end DifferentialGeometry.Geometry.Collapse
