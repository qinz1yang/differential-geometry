import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.BundleEquivalence
import DifferentialGeometry.Geometry.Connection.TensorNabla.TotalPullback
import DifferentialGeometry.Geometry.Operator.MetricTracePullback
import DifferentialGeometry.Bundle.Hom.Regularity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem exists_uhlenbeck_tensor_covariantDerivative_intertwining
    [I.Boundaryless]
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (hS : IsSolutionOn (I := I) S)
    {s t : Real} (hs : 0 < s) (hst : s < t) (htT : t < T) :
    ∃ (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
      (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
        (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
          TotalSpace (E →L[Real] E)
            (fun x => TangentSpace I x →L[Real] TangentSpace I x)))),
      (∀ x : M, ∀ v w : TangentSpace I x,
        (S.family.metric t).inner x (φ x v) (φ x w) =
          (S.family.metric s).inner x v w) ∧
      (let cov := metricCov (S.family.metric t)
       let D := CovariantDerivative.pullbackFiberwiseLinearEquiv
         (fun y => (φ y).toLinearEquiv) (hφ.of_le (by norm_num)).clm_bundle_map cov
       ∀ (k : Nat) (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) k)
         (x : M) (X : TangentSpace I x) (tail : Fin k → TangentSpace I x),
         D.multilinear k
             (fun y => tensor0SPullbackCLE k (φ y).toLinearEquiv (A y))
             x (φ x X) tail =
           tensor0SPullbackCLE (k + 1) (φ x).toLinearEquiv
             (totalNabla0SFun k cov A x) (Fin.cons X tail)) ∧
      ∀ (k : Nat) (x : M) (A : Tensor0SSpace (k + 2) I x),
        metricTraceFirstTwo0STensor (S.family.metric s)
            (tensor0SPullbackCLE (k + 2) (φ x).toLinearEquiv A) =
          tensor0SPullbackCLE k (φ x).toLinearEquiv
            (metricTraceFirstTwo0STensor (S.family.metric t) A) := by
  obtain ⟨phi, hphi, _, hiso⟩ :=
    exists_uhlenbeck_tangent_bundle_isometry hT S hS hs hst htT
  let φ := fun x => (phi x).toContinuousLinearEquiv
  have hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))) :=
    ContMDiff.clm_bundle_of_map hphi
  refine ⟨φ, hφ, hiso, ?_, ?_⟩
  · dsimp only
    intro k A x X tail
    exact multilinear_pullback_eq_totalNabla0SFun φ (hφ.of_le (by norm_num))
      k (metricCov (S.family.metric t)) A x X tail
  · intro k x A
    exact metricTraceFirstTwo0STensor_tensor0SPullbackCLE
      (S.family.metric s) (S.family.metric t) (φ x).toLinearEquiv (hiso x) A

end DifferentialGeometry.PDE.RicciFlow
