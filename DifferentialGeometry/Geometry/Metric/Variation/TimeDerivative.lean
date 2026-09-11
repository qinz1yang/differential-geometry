import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

def metricTimeDerivWithin (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    {r : ℕ} {x : M} (A : ℝ → Tensor0SSpace r I x) (t : ℝ) :
    Tensor0SSpace r I x :=
  derivWithin A J t + covariantEndomorphismAction0S (A t) (ricciSharp (g t) x)

def iteratedMetricTimeDerivWithin (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) {r : ℕ} {x : M} (A : ℝ → Tensor0SSpace r I x) :
    ℕ → ℝ → Tensor0SSpace r I x
  | 0 => A
  | b + 1 => metricTimeDerivWithin g J (iteratedMetricTimeDerivWithin g J A b)

@[simp] theorem iteratedMetricTimeDerivWithin_zero
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    {r : ℕ} {x : M} (A : ℝ → Tensor0SSpace r I x) :
    iteratedMetricTimeDerivWithin g J A 0 = A := rfl

@[simp] theorem iteratedMetricTimeDerivWithin_succ
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    {r : ℕ} {x : M} (A : ℝ → Tensor0SSpace r I x) (b : ℕ) :
    iteratedMetricTimeDerivWithin g J A (b + 1) =
      metricTimeDerivWithin g J (iteratedMetricTimeDerivWithin g J A b) := rfl

theorem metricTimeDerivWithin_eq_of_hasDerivWithinAt
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    {r : ℕ} {x : M} {A : ℝ → Tensor0SSpace r I x}
    {t : ℝ} {A' : Tensor0SSpace r I x}
    (hA : HasDerivWithinAt A A' J t) (hJ : UniqueDiffWithinAt ℝ J t) :
    metricTimeDerivWithin g J A t =
      A' + covariantEndomorphismAction0S (A t) (ricciSharp (g t) x) := by
  exact congrArg
    (fun B : Tensor0SSpace r I x =>
      B + covariantEndomorphismAction0S (A t) (ricciSharp (g t) x))
    (hA.derivWithin hJ)

theorem metricTimeDerivWithin_apply
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    {r : ℕ} {x : M} {A : ℝ → Tensor0SSpace r I x} {t : ℝ}
    (hA : DifferentiableWithinAt ℝ A J t) (hJ : UniqueDiffWithinAt ℝ J t)
    (v : Fin r → TangentSpace I x) :
    metricTimeDerivWithin g J A t v =
      derivWithin (fun s => A s v) J t +
        ∑ i : Fin r, A t (Function.update v i (ricciSharp (g t) x (v i))) := by
  have hev := (tensor0SEvalCLM (I := I) v).hasFDerivAt.comp_hasDerivWithinAt
    t hA.hasDerivWithinAt
  have heq : derivWithin (fun s => A s v) J t = derivWithin A J t v :=
    hev.derivWithin hJ
  rw [metricTimeDerivWithin, Tensor0SSpace.add_apply,
    covariantEndomorphismAction0S_apply, heq]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
