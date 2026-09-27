import DifferentialGeometry.Geometry.Connection.MetricTrace.Relowering
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Relowering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Curvature.AlgebraicBridge
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

section ReLower

omit [SigmaCompactSpace M] in
theorem reLower_rm04 (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (x : M) (hRm : Rm2 x = metricRm04At (I := I) g₂ x)
    (X Y Z W : TangentSpace I x) :
    Tensor0SSpace.eval (reLower (I := I) g₁ g₂ Rm2 x)
        (vec4 (I := I) X Y Z W) =
      g₁.inner x (riemannOp (metricCov (I := I) g₂) x X Y Z) W := by
  classical
  have hlast : (vec4 (I := I) X Y Z W) (Fin.last 3) = W := by
    simp [vec4]
  have hupd : Function.update (vec4 (I := I) X Y Z W) (Fin.last 3)
      (sharpFlat (I := I) g₁ g₂ x W) =
      vec4 (I := I) X Y Z (sharpFlat (I := I) g₁ g₂ x W) := by
    funext i
    fin_cases i <;> simp [vec4, Function.update]
  rw [reLower_apply (I := I) g₁ g₂ Rm2 x, hlast, hupd, hRm]
  exact mixLow_eq_rm04 (I := I) g₁ g₂ x X Y Z W

end ReLower

section Defect

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
private theorem metricCov_one (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (I := I) (E := E) (M := M) (metricCov (I := I) g) (1 : WithTop ℕ∞) := by
  simpa [metricCov] using
    (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) g)

end Defect

section Payoff

def reLowerOp (g₁ g₂ : SmoothRiemannianMetric I M) :
    ∀ k : ℕ, Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) k
  | 0 => id
  | (_ + 1) => fun T => reLower (I := I) g₁ g₂ T

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
@[simp] theorem reLowerOp_succ (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    reLowerOp (I := I) g₁ g₂ (k + 1) T = reLower (I := I) g₁ g₂ T := rfl

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapCommFlux_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    lapCommFlux (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T =
      reLowerPair (I := I) g₂ T
        (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁)) := by
  rw [lapCommFlux, reLowerOp_succ, reLowerOp_succ, nabla_reLower]
  abel

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) +
        lapCommRem (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T := by
  have h := lapComm_eq_div_flux (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T
  rw [lapCommFlux_reLower (I := I) g₁ g₂ T] at h
  simpa using h

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapCommRem_reLower (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    lapCommRem (I := I) g₂ (reLowerOp (I := I) g₁ g₂) T =
      metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
        (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
          (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapCommRem, reLowerOp_succ, reLowerOp_succ, covDiv0SField, covDiv0SField,
    nabla_reLower, metricTraceFirstTwoField_add, trace_reLower]
  abel

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower_eq (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) +
        metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
          (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
            (metricNabla0S (I := I) g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapComm_reLower (I := I) g₁ g₂ T, lapCommRem_reLower (I := I) g₁ g₂ T]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lapComm_reLower_flux (g₁ g₂ : SmoothRiemannianMetric I M) {k : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (k + 1)) :
    roughLap0SField (I := I) g₂ (reLower (I := I) g₁ g₂ T) -
        reLower (I := I) g₁ g₂ (roughLap0SField (I := I) g₂ T) =
      covDiv0SField (I := I) g₂
          (reLowerPair (I := I) g₂ T
            (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁))) +
        metricTraceFirstTwoField (I := I) (M := M) (s := k + 1) g₂
          (reLowerPair (I := I) g₂ (metricNabla0S (I := I) g₂ T)
            (-lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₁))) := by
  rw [lapComm_reLower_eq (I := I) g₁ g₂ T, nabla2_metric1 (I := I) g₁ g₂]

end Payoff

end DifferentialGeometry.PDE.RicciFlow

end
