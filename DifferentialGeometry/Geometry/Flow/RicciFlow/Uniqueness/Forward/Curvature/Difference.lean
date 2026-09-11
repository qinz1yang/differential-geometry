import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.DifferenceFields
import DifferentialGeometry.Geometry.Operator.CovariantTensor

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]


section DivergenceForm

variable {s : ℕ}

def lapDiffFlux (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  metricNabla0S (I := I) g₁ T - metricNabla0S (I := I) g₂ T

omit [SigmaCompactSpace M] in
theorem lapDiffFlux_apply (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    lapDiffFlux (I := I) g₁ g₂ T x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
          (metricCov (I := I) g₁) T x -
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
          (metricCov (I := I) g₂) T x := rfl

omit [SigmaCompactSpace M] in
@[simp] theorem lapDiffFlux_self (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    lapDiffFlux (I := I) g g T = 0 :=
  sub_self _

def lapDiffRem (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  metricTraceFirstTwoField (I := I) (M := M) g₁
      (lapDiffFlux (I := I) g₁ g₂ (metricNabla0S (I := I) g₂ T)) +
    (metricTraceFirstTwoField (I := I) (M := M) g₁
        (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T)) -
      metricTraceFirstTwoField (I := I) (M := M) g₂
        (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T)))

omit [SigmaCompactSpace M] in
@[simp] theorem lapDiffRem_self (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    lapDiffRem (I := I) g g T = 0 := by
  rw [lapDiffRem, lapDiffFlux_self, traceFirstTwo_zero, sub_self, add_zero]

omit [SigmaCompactSpace M] in
theorem lapDiff_eq_div_flux (g₁ g₂ : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    roughLap0SField (I := I) g₁ T - roughLap0SField (I := I) g₂ T =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) +
        lapDiffRem (I := I) g₁ g₂ T := by
  have hdiv :
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ T) =
        roughLap0SField (I := I) g₁ T -
          covDiv0SField (I := I) g₁ (metricNabla0S (I := I) g₂ T) := by
    rw [lapDiffFlux, covDiv0SField_sub, roughLap0SField]
  have hrem :
      lapDiffRem (I := I) g₁ g₂ T =
        (covDiv0SField (I := I) g₁ (metricNabla0S (I := I) g₂ T) -
            metricTraceFirstTwoField (I := I) (M := M) g₁
              (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T))) +
          (metricTraceFirstTwoField (I := I) (M := M) g₁
              (metricNabla0S (I := I) g₂ (metricNabla0S (I := I) g₂ T)) -
            roughLap0SField (I := I) g₂ T) := by
    rw [lapDiffRem, lapDiffFlux, traceFirstTwo_sub, roughLap0SField, covDiv0SField,
      covDiv0SField]
  rw [hdiv, hrem]
  abel

end DivergenceForm

section Curvature

def rmDiffFlux (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x :=
  lapDiffFlux (I := I) g₁ g₂ Rm2 x

omit [SigmaCompactSpace M] in
theorem rmDiffFlux_apply (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    rmDiffFlux (I := I) g₁ g₂ Rm2 x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
          (metricCov (I := I) g₁) Rm2 x -
        totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4
          (metricCov (I := I) g₂) Rm2 x := rfl

omit [SigmaCompactSpace M] [T2Space M] in
theorem rm2Low_eq_sub (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        (I := I) g₁ (metricCov (I := I) g₂) (metricCov_smooth (I := I) g₂) x =
      metricRm04At (I := I) g₁ x - rmDiffLowAt (I := I) g₁ g₂ x :=
  (sub_sub_cancel _ _).symm

omit [SigmaCompactSpace M] in
theorem rmLapDiff_div_flux (g₁ g₂ : SmoothRiemannianMetric I M)
    (Rm2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4) (x : M) :
    roughLap0SField (I := I) g₁ Rm2 x - roughLap0SField (I := I) g₂ Rm2 x =
      covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ Rm2) x +
        lapDiffRem (I := I) g₁ g₂ Rm2 x := by
  have h := lapDiff_eq_div_flux (I := I) g₁ g₂ Rm2
  have hsub :
      (roughLap0SField (I := I) g₁ Rm2 - roughLap0SField (I := I) g₂ Rm2) x =
        roughLap0SField (I := I) g₁ Rm2 x - roughLap0SField (I := I) g₂ Rm2 x := rfl
  have hadd :
      (covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ Rm2) +
          lapDiffRem (I := I) g₁ g₂ Rm2) x =
        covDiv0SField (I := I) g₁ (lapDiffFlux (I := I) g₁ g₂ Rm2) x +
          lapDiffRem (I := I) g₁ g₂ Rm2 x := rfl
  rw [← hsub, ← hadd, h]

end Curvature

end DifferentialGeometry.PDE.RicciFlow

end
