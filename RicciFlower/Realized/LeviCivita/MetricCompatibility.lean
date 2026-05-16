import RicciFlower.Realized.LeviCivita.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Metric Compatibility Calculus

Concrete apply theorems for the realized metric-compatibility predicate.
-/

namespace RicciFlower
namespace Realized
namespace LeviCivita

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

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

/-- Family metric compatibility at a flow time. -/
theorem metric_compatible_family_apply
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hmc : IsMetricCompatibleFamilyOn (I := I) G)
    (t : RealTimeInterval.FlowTime D)
    {x : M}
    (X Y Z : (p : M) -> TangentSpace I p)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mfderiv I 𝓘(Real, Real)
        (fun y : M => (G.metricAt t).inner y (Y y) (Z y)) x (X x) =
      (G.metricAt t).inner x ((G.connectionAt t) Y x (X x)) (Z x) +
        (G.metricAt t).inner x (Y x) ((G.connectionAt t) Z x (X x)) :=
  metric_compatible_apply (I := I) (hmc t) X Y Z hX hY hZ

end LeviCivita
end Realized
end RicciFlower
