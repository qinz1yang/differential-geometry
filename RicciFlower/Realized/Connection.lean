import RicciFlower.Realized.MetricFamily
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# RicciFlower Realized Connection Predicates

Connection smoothness, metric compatibility, torsion freedom, and Levi-Civita
conditions are exposed as predicates and theorem accessors around the realized
metric-family data. They are not stored in `RealizedMetricFamily`.
-/

namespace RicciFlower
namespace Realized

open Bundle
open CovariantDerivative
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

section Smoothness

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- Spatial smoothness of each connection in a realized family.

This is a predicate interface; consumers can require it where needed. -/
def ConnectionFamilySmooth
    (G : RealizedMetricFamily (I := I) (M := M) Time) : Prop :=
  forall t : Time, ContMDiffCovariantDerivative (G.connection t) ∞

/-- Extract smoothness at a fixed time from the predicate interface. -/
theorem connection_smooth_at_of_connectionFamilySmooth
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (hG : ConnectionFamilySmooth G) (t : Time) :
    ContMDiffCovariantDerivative (G.connection t) ∞ :=
  hG t

/-- Spatial smoothness of each connection over a concrete real time interval. -/
def ConnectionFamilySmoothOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop :=
  forall t : RealTimeInterval.FlowTime D, ContMDiffCovariantDerivative (G.connectionAt t) ∞

/-- Extract smoothness at a flow time from the interval predicate. -/
theorem connection_smooth_at_of_connectionFamilySmoothOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : ConnectionFamilySmoothOn (I := I) (M := M) G)
    (t : RealTimeInterval.FlowTime D) :
    ContMDiffCovariantDerivative (G.connectionAt t) ∞ :=
  hG t

end Smoothness

section Compatibility

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M]

/-- Mathlib-level metric compatibility for a realized covariant derivative and metric.

This is stated directly through the manifold derivative of the scalar function
`x ↦ g_x(Y_x,Z_x)`, avoiding any bridge to the old synthetic layer. -/
def IsMetricCompatibleMathlib
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) : Prop :=
  forall (X Y Z : (x : M) -> TangentSpace I x) (x : M),
    mfderiv I 𝓘(Real, Real) (fun y : M => g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (cov Y x (X x)) (Z x) + g.inner x (Y x) (cov Z x (X x))

/-- Mathlib-level metric compatibility at every time. -/
def IsMetricCompatibleFamily
    (G : RealizedMetricFamily (I := I) (M := M) Time) : Prop :=
  forall t : Time, IsMetricCompatibleMathlib (I := I) (M := M) (G.connection t) (G.metric t)

/-- Zero torsion at every time. -/
def IsTorsionFreeFamily
    (G : RealizedMetricFamily (I := I) (M := M) Time) : Prop :=
  forall t : Time, (G.connection t).torsion = 0

/-- Levi-Civita family predicate, stated outside the metric-family data. -/
def IsLeviCivitaFamily
    (G : RealizedMetricFamily (I := I) (M := M) Time) : Prop :=
  IsMetricCompatibleFamily G /\ IsTorsionFreeFamily G

theorem metric_compatible_of_isLeviCivitaFamily
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (hG : IsLeviCivitaFamily G) :
    IsMetricCompatibleFamily G :=
  hG.1

theorem torsion_free_of_isLeviCivitaFamily
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (hG : IsLeviCivitaFamily G) :
    IsTorsionFreeFamily G :=
  hG.2

theorem metric_compatible_at_of_isLeviCivitaFamily
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (hG : IsLeviCivitaFamily G) (t : Time) :
    IsMetricCompatibleMathlib (I := I) (M := M) (G.connection t) (G.metric t) :=
  hG.1 t

theorem torsion_free_at_of_isLeviCivitaFamily
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (hG : IsLeviCivitaFamily G) (t : Time) :
    (G.connection t).torsion = 0 :=
  hG.2 t

theorem isLeviCivitaFamily_of_parts
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (hmc : IsMetricCompatibleFamily G) (htf : IsTorsionFreeFamily G) :
    IsLeviCivitaFamily G :=
  ⟨hmc, htf⟩

end Compatibility

end Realized
end RicciFlower
