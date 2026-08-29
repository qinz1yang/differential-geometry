import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Christoffel
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

section Carriers

def metricDiffAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  metricTensorField (I := I) g₁ x - metricTensorField (I := I) g₂ x

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem metricDiffAt_apply (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricDiffAt (I := I) g₁ g₂ x v =
      g₁.inner x (v 0) (v 1) - g₂.inner x (v 0) (v 1) := by
  have h : metricDiffAt (I := I) g₁ g₂ x v =
      metricTensorField (I := I) g₁ x v - metricTensorField (I := I) g₂ x v :=
    Tensor0SSpace.sub_apply (I := I) 2 x
      (metricTensorField (I := I) g₁ x) (metricTensorField (I := I) g₂ x) v
  rw [h, metricTensorField_apply, metricTensorField_apply]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem metricDiffAt_self (g : SmoothRiemannianMetric I M) (x : M) :
    metricDiffAt (I := I) g g x = 0 :=
  sub_self _

omit [SigmaCompactSpace M] in
private theorem covDiff_self
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M) :
    CovariantDerivative.difference cov cov x = 0 := by
  classical
  refine ContinuousLinearMap.ext fun w => ?_
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M -> Type _)) x w
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have h := IsCovariantDerivativeOn.difference_apply
    cov.isCovariantDerivativeOnUniv cov.isCovariantDerivativeOnUniv
    (x := x) (Set.mem_univ x) (σ := fun y => σ y) hσ
  rw [sub_self] at h
  rw [← hσx]
  simpa [CovariantDerivative.difference] using h

private def connectionDifferenceOutAt (g : SmoothRiemannianMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M) :
    Tensor0SSpace 3 I x :=
  Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (DifferentialGeometry.Integral.L2.lowerAllUpperIndices (I := I) (M := M) g 1 2 x
      (TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (connectionDifferenceTensorAt (I := I) cov cov' x)))

private def connectionDifferenceStdPerm : Equiv.Perm (Fin 3) where
  toFun i := if i = 0 then 2 else if i = 1 then 0 else 1
  invFun i := if i = 0 then 1 else if i = 1 then 2 else 0
  left_inv i := by fin_cases i <;> simp
  right_inv i := by fin_cases i <;> simp

omit [SigmaCompactSpace M] [T2Space M] in
private theorem connectionDifferenceOutAt_apply (g : SmoothRiemannianMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M)
    (w : Fin 3 -> TangentSpace I x) :
    connectionDifferenceOutAt (I := I) g cov cov' x w =
      g.inner x (w 0) (CovariantDerivative.difference cov cov' x (w 2) (w 1)) := by
  change
    DifferentialGeometry.Integral.L2.lowerAllUpperIndices (I := I) (M := M) g 1 2 x
        (TensorRSSpace.toModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (connectionDifferenceTensorAt (I := I) cov cov' x))
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (w i)) = _
  rw [DifferentialGeometry.Integral.L2.lowerAllUpperIndices_apply]
  change
    Tensor0SSpace.eval
      (connectionDifferenceOutput (I := I) (CovariantDerivative.difference cov cov' x)
        (Tensor0SSpace.ofModel (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (DifferentialGeometry.Integral.L2.separableFormAt (I := I) (M := M) g x 1
            (fun i : Fin 1 =>
              tangentSpaceModelContinuousLinearEquiv (I := I) x (w (Fin.castAdd 2 i))))))
        (fun j : Fin 2 => w (Fin.natAdd 1 j)) = _
  rw [connectionDifferenceOutput_apply]
  change
    DifferentialGeometry.Integral.L2.separableFormAt (I := I) (M := M) g x 1
        (fun i : Fin 1 =>
          tangentSpaceModelContinuousLinearEquiv (I := I) x (w (Fin.castAdd 2 i)))
        (fun _ : Fin 1 =>
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            (CovariantDerivative.difference cov cov' x
              (w (Fin.natAdd 1 (1 : Fin 2))) (w (Fin.natAdd 1 (0 : Fin 2))))) = _
  rw [DifferentialGeometry.Integral.L2.separableFormAt_apply]
  simp only [DifferentialGeometry.Integral.L2.modelInnerAt_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  simp

def connectionDifferenceLowAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 3 I x :=
  ContinuousMultilinearMap.domDomCongr connectionDifferenceStdPerm
    (connectionDifferenceOutAt (I := I) g₁ (metricCov (I := I) g₁) (metricCov (I := I) g₂) x)

omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceLowAt_apply (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 3 -> TangentSpace I x) :
    Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g₁ g₂ x) v =
      g₁.inner x
        (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
          (v 1) (v 0))
        (v 2) := by
  have h : Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g₁ g₂ x) v =
      g₁.inner x (v 2)
        (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
          (v 1) (v 0)) :=
    connectionDifferenceOutAt_apply (I := I) g₁ (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
      (fun i : Fin 3 => v (connectionDifferenceStdPerm i))
  rw [h]
  exact g₁.symm x (v 2)
    (CovariantDerivative.difference (metricCov (I := I) g₁) (metricCov (I := I) g₂) x
      (v 1) (v 0))

omit [SigmaCompactSpace M] in
@[simp]
theorem connectionDifferenceLowAt_self (g : SmoothRiemannianMetric I M) (x : M) :
    connectionDifferenceLowAt (I := I) g g x = 0 := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  change Tensor0SSpace.eval (connectionDifferenceLowAt (I := I) g g x) v =
    Tensor0SSpace.eval 0 v
  rw [connectionDifferenceLowAt_apply, covDiff_self]
  change g.inner x 0 (v 2) = 0
  rw [map_zero (g.inner x), zero_apply]

def rmDiffLowAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
      (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x -
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
      (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x

omit [SigmaCompactSpace M] [T2Space M] in
theorem rmDiffLowAt_apply (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 4 -> TangentSpace I x) :
    rmDiffLowAt (I := I) g₁ g₂ x v =
      metricRm04At (I := I) g₁ x v -
        DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x v :=
  Tensor0SSpace.sub_apply (I := I) 4 x _ _ v

omit [SigmaCompactSpace M] [T2Space M] in
theorem rmDiffLowAt_std (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    rmDiffLowAt (I := I) g₁ g₂ x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      metricRm13At (I := I) g₁ x
          (dualToCotangentGen (I := I) (tangentFlatLinearGen (I := I) g₁ x W))
          (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z) -
        metricRm13At (I := I) g₂ x
          (dualToCotangentGen (I := I) (tangentFlatLinearGen (I := I) g₁ x W))
          (DifferentialGeometry.Geometry.Curvature.vec3 (I := I) X Y Z) := by
  have hsub : rmDiffLowAt (I := I) g₁ g₂ x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) x
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) -
        DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
          (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) :=
    Tensor0SSpace.sub_apply (I := I) 4 x _ _ _
  rw [hsub,
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_eq_lower_riemannCurvatureAt
      (I := I) g₁ (metricCov (I := I) g₁) (metricCov_smooth (I := I) g₁) X Y Z W,
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_eq_lower_riemannCurvatureAt
      (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) X Y Z W]
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem rmDiffLowAt_self (g : SmoothRiemannianMetric I M) (x : M) :
    rmDiffLowAt (I := I) g g x = 0 :=
  sub_self _

end Carriers

section Norms

def metricDiffSq (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Real :=
  normSq0S (I := I) g₁ x 2 (metricDiffAt (I := I) g₁ g₂ x)

def connectionDifferenceSq (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Real :=
  normSq0S (I := I) g₁ x 3 (connectionDifferenceLowAt (I := I) g₁ g₂ x)

def rmDiffSq (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Real :=
  normSq0S (I := I) g₁ x 4 (rmDiffLowAt (I := I) g₁ g₂ x)

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricDiffSq_def (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    metricDiffSq (I := I) g₁ g₂ x =
      normSq0S (I := I) g₁ x 2 (metricDiffAt (I := I) g₁ g₂ x) := rfl

omit [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifferenceSq_def (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    connectionDifferenceSq (I := I) g₁ g₂ x =
      normSq0S (I := I) g₁ x 3 (connectionDifferenceLowAt (I := I) g₁ g₂ x) := rfl

omit [SigmaCompactSpace M] [T2Space M] in
theorem rmDiffSq_def (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    rmDiffSq (I := I) g₁ g₂ x =
      normSq0S (I := I) g₁ x 4 (rmDiffLowAt (I := I) g₁ g₂ x) := rfl

end Norms

end DifferentialGeometry.PDE.RicciFlow

end
