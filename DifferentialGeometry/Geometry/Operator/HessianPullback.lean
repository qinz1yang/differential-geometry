import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import DifferentialGeometry.Geometry.Operator.MetricTracePullback
import DifferentialGeometry.Geometry.Connection.TensorNabla.TotalPullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
theorem tensor0SPullbackCLE_duSec_apply
    (u : M → Real) (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    {x y : M} (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (X : TangentSpace I x) :
    tensor0SPullbackCLE 1 e (duSec (I := I) u hu y) (fun _ => X) =
      mvfderiv (I := I) u y (e X) := by
  rw [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply, duSec_apply]
  exact differential1FormFun_apply_eq_mvfderiv u y (e X)

theorem multilinear_pullback_eq_hessianSec
    (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (u : M → Real) (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    (x : M) (X : TangentSpace I x) (tail : Fin 1 → TangentSpace I x) :
    CovariantDerivative.multilinear
        (CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) 1
        (fun y => tensor0SPullbackCLE 1 (φ y).toLinearEquiv (duSec (I := I) u hu y))
        x (φ x X) tail =
      tensor0SPullbackCLE 2 (φ x).toLinearEquiv
        (hessianSec cov hcov u hu x) (Fin.cons X tail) := by
  exact multilinear_pullback_eq_totalNabla0SFun
    φ hφ 1 cov (duSec (I := I) u hu) x X tail

theorem metricTracePair0SAt_tensor0SPullbackCLE_hessianSec
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (gSource gTarget : SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible cov gTarget)
    (u : M → Real) (hu : ContMDiff I 𝓘(Real, Real) ∞ u)
    {x y : M} (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ v w, gTarget.inner y (e v) (e w) = gSource.inner x v w) :
    metricTracePair0SAt gSource
        (tensor0SPullbackCLE 2 e (hessianSec cov hcov u hu y)) =
      laplacian cov gTarget u y := by
  rw [metricTracePair0SAt_tensor0SPullbackCLE gSource gTarget e hiso]
  exact (ScalarLaplacianRealizesTraceAt.eq_trace cov gTarget u _
    (scalarLap_smooth cov hcov gTarget hmc u hu)).symm

end DifferentialGeometry.Geometry.Operator
