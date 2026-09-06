import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Kernel
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricPullback
import DifferentialGeometry.Tensor.Alternating.Comp

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

omit [CompleteSpace E] [T2Space M] in
theorem tensor0SPullbackCLE_twoFormTensorAt_congrLeft
    {x y : M} (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    tensor0SPullbackCLE (I := I) (M := M) 2 e
        (twoFormTensorAt (I := I)
          (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
            (ι := Fin 2) a)) =
      twoFormTensorAt (I := I) a := by
  apply tensor0SSpace_ext 2 x
  intro v
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply,
    twoFormTensorAt_apply]
  change a (fun i => e.symm (e (v i))) = a v
  congr 1
  funext i
  rw [e.symm_apply_apply]

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorPairingAt_congrLeft
    (gSource gTarget : SmoothRiemannianMetric I M) (x y : M)
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) =
      gSource.inner x u v)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorPairingAt (I := I) gTarget y A
        (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
          (ι := Fin 2) a)
        (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
          (ι := Fin 2) b) =
      curvatureOperatorPairingAt (I := I) gSource x
        (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A) a b := by
  unfold curvatureOperatorPairingAt
  congr 1
  rw [← Tensor0SBundle.inner0S_tensor0SPullbackCLE
    (I := I) gSource gTarget x y 4 e hiso]
  have hproduct :
      tensor0SPullbackCLE (I := I) (M := M) 4 e
          (Tensor0SSpace.product
            (twoFormTensorAt (I := I)
              (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
                (ι := Fin 2) a))
            (twoFormTensorAt (I := I)
              (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
                (ι := Fin 2) b))) =
        Tensor0SSpace.product
          (tensor0SPullbackCLE (I := I) (M := M) 2 e
            (twoFormTensorAt (I := I)
              (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
                (ι := Fin 2) a)))
          (tensor0SPullbackCLE (I := I) (M := M) 2 e
            (twoFormTensorAt (I := I)
              (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
                (ι := Fin 2) b))) := by
    simpa using Tensor0SBundle.tensor0SPullbackCLE_product
      (I := I) (r := 2) (s := 2) e
      (twoFormTensorAt (I := I)
        (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
          (ι := Fin 2) a))
      (twoFormTensorAt (I := I)
        (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
          (ι := Fin 2) b))
  rw [hproduct,
    tensor0SPullbackCLE_twoFormTensorAt_congrLeft,
    tensor0SPullbackCLE_twoFormTensorAt_congrLeft]
  rfl

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorKernelAt_map_congrLeft
    (gSource gTarget : SmoothRiemannianMetric I M) (x y : M)
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) =
      gSource.inner x u v)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
    Submodule.map
        (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
          (ι := Fin 2)).toLinearMap
        (curvatureOperatorKernelAt (I := I) gSource x
          (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A)) =
      curvatureOperatorKernelAt (I := I) gTarget y A := by
  let F :
      (TangentSpace I x [⋀^Fin 2]→L[Real] Real) ≃L[Real]
        (TangentSpace I y [⋀^Fin 2]→L[Real] Real) :=
    e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft (ι := Fin 2)
  apply le_antisymm
  · rintro beta ⟨alpha, halpha, rfl⟩
    intro gamma
    let delta := F.symm gamma
    have hpair := curvatureOperatorPairingAt_congrLeft
      (I := I) gSource gTarget x y e hiso A alpha delta
    have hdelta :
        e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
            (ι := Fin 2) delta = gamma := by
      change F (F.symm gamma) = gamma
      exact F.apply_symm_apply gamma
    rw [hdelta] at hpair
    have hpair' :
        curvatureOperatorPairingAt (I := I) gTarget y A
            (F alpha) gamma =
          curvatureOperatorPairingAt (I := I) gSource x
            (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A)
            alpha delta := by
      exact hpair
    change curvatureOperatorPairingAt (I := I) gTarget y A (F alpha) gamma = 0
    rw [hpair']
    exact halpha delta
  · intro beta hbeta
    refine ⟨F.symm beta, ?_, F.apply_symm_apply beta⟩
    intro alpha
    have hpair := curvatureOperatorPairingAt_congrLeft
      (I := I) gSource gTarget x y e hiso A (F.symm beta) alpha
    have hbetaApply :
        e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
            (ι := Fin 2) (F.symm beta) = beta := by
      change F (F.symm beta) = beta
      exact F.apply_symm_apply beta
    rw [hbetaApply] at hpair
    have hpair' :
        curvatureOperatorPairingAt (I := I) gTarget y A beta (F alpha) =
          curvatureOperatorPairingAt (I := I) gSource x
            (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A)
            (F.symm beta) alpha := by
      exact hpair
    rw [← hpair']
    exact hbeta (F alpha)

end DifferentialGeometry.Geometry.Curvature
