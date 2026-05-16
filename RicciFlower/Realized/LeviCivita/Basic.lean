import RicciFlower.Realized.Connection

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Levi-Civita Calculus Predicates

This file gives RicciFlower-facing predicates for metric compatibility,
torsion-freeness, and Levi-Civita calculus.  These are explicit packages around
realized metric/connection data, not typeclass instances.
-/

namespace RicciFlower
namespace Realized
namespace LeviCivita

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Pointwise

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M]

/-- Metric compatibility at a point, stated on differentiable tangent fields.

This is the concrete realized form of
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

/-- Torsion-freeness at a point. -/
def IsTorsionFreeAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M) : Prop :=
  cov.torsion x = 0

/-- Levi-Civita predicate at a point. -/
def IsLeviCivitaAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) (x : M) : Prop :=
  IsMetricCompatibleAt (I := I) cov g x /\ IsTorsionFreeAt (I := I) cov x

/-- Metric compatibility at every point. -/
def IsMetricCompatible
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) : Prop :=
  forall x : M, IsMetricCompatibleAt (I := I) cov g x

/-- Torsion-freeness at every point. -/
def IsTorsionFree
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) : Prop :=
  forall x : M, IsTorsionFreeAt (I := I) cov x

/-- Levi-Civita predicate for a single metric and connection. -/
def IsLeviCivita
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) : Prop :=
  IsMetricCompatible (I := I) cov g /\ IsTorsionFree (I := I) cov

theorem metricCompatible_of_isLeviCivita
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (h : IsLeviCivita (I := I) cov g) :
    IsMetricCompatible (I := I) cov g :=
  h.1

theorem torsionFree_of_isLeviCivita
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (h : IsLeviCivita (I := I) cov g) :
    IsTorsionFree (I := I) cov :=
  h.2

theorem isLeviCivita_of_parts
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hmc : IsMetricCompatible (I := I) cov g)
    (htf : IsTorsionFree (I := I) cov) :
    IsLeviCivita (I := I) cov g :=
  ⟨hmc, htf⟩

end Pointwise

section Family

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M]

/-- Metric compatibility for an interval metric family. -/
def IsMetricCompatibleFamilyOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop :=
  forall t : RealTimeInterval.FlowTime D,
    IsMetricCompatible (I := I) (G.connectionAt t) (G.metricAt t)

/-- Torsion-freeness for an interval metric family. -/
def IsTorsionFreeFamilyOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop :=
  forall t : RealTimeInterval.FlowTime D,
    IsTorsionFree (I := I) (G.connectionAt t)

/-- Levi-Civita predicate for an interval family. -/
def IsLeviCivitaFamilyOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop :=
  IsMetricCompatibleFamilyOn (I := I) G /\ IsTorsionFreeFamilyOn (I := I) G

/-- Explicit theorem package for Levi-Civita calculus on a time interval. -/
structure LeviCivitaCalculusOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop where
  metricCompatible : IsMetricCompatibleFamilyOn (I := I) G
  torsionFree : IsTorsionFreeFamilyOn (I := I) G

theorem isLeviCivitaFamilyOn_of_calculus
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hG : LeviCivitaCalculusOn (I := I) G) :
    IsLeviCivitaFamilyOn (I := I) G :=
  ⟨hG.metricCompatible, hG.torsionFree⟩

end Family

end LeviCivita
end Realized
end RicciFlower
