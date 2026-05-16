import RicciFlower.Metric.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Metric-Compatible Connections

This file contains predicates and apply theorems for arbitrary
metric-compatible connections.  These are ordinary connection facts, not
realization predicates.
-/

namespace RicciFlower
namespace Connection

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Pointwise

/-- Metric compatibility at a point, stated on differentiable tangent fields.

This is the concrete form of
`X <Y,Z> = <nabla_X Y, Z> + <Y, nabla_X Z>`. -/
def IsMetricCompatibleAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) (x : M) : Prop :=
  forall (X Y Z : (p : M) -> TangentSpace I p),
    MDiffAt (T% X) x ->
      MDiffAt (T% Y) x ->
        MDiffAt (T% Z) x ->
          mfderiv I 𝓘(Real, Real) (fun y : M => g.inner y (Y y) (Z y)) x (X x) =
            g.inner x (cov Y x (X x)) (Z x) +
              g.inner x (Y x) (cov Z x (X x))

/-- Metric compatibility at every point. -/
def IsMetricCompatible
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) : Prop :=
  forall x : M, IsMetricCompatibleAt (I := I) cov g x

/-- Pointwise metric compatibility:
`X <Y,Z> = <nabla_X Y,Z> + <Y,nabla_X Z>`. -/
theorem metric_compatible_at_apply
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M} {x : M}
    (hmc : IsMetricCompatibleAt (I := I) cov g x)
    (X Y Z : (p : M) -> TangentSpace I p)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mfderiv I 𝓘(Real, Real) (fun y : M => g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (cov Y x (X x)) (Z x) +
        g.inner x (Y x) (cov Z x (X x)) :=
  hmc X Y Z hX hY hZ

/-- Global metric compatibility at a point. -/
theorem metric_compatible_apply
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hmc : IsMetricCompatible (I := I) cov g)
    {x : M}
    (X Y Z : (p : M) -> TangentSpace I p)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mfderiv I 𝓘(Real, Real) (fun y : M => g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (cov Y x (X x)) (Z x) +
        g.inner x (Y x) (cov Z x (X x)) :=
  metric_compatible_at_apply (I := I) (hmc x) X Y Z hX hY hZ

end Pointwise

end Connection
end RicciFlower
