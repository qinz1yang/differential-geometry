import RicciFlower.Realized.MetricFamily

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# RicciFlower Connection Smoothness

Connection smoothness is exposed as a predicate around realized metric-family
data. Metric compatibility, torsion freedom, and Levi-Civita predicates live in
`RicciFlower.LeviCivita.Basic`; the canonical metric-derived
connection is constructed in `RicciFlower.LeviCivita.Koszul`.
-/

namespace RicciFlower
namespace Connection

open Bundle
open CovariantDerivative
open Realized
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

end Connection
end RicciFlower
