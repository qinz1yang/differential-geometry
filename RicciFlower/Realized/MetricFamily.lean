import RicciFlower.Analysis.Time
import RicciFlower.Connection.MetricCompatibility
import RicciFlower.Metric.Basic
import RicciFlower.Realized.TimeInterval
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# RicciFlower Realized Metric Families

The realized V2 core stores the geometric objects: a time-indexed Riemannian
metric, a time-indexed mathlib covariant derivative on the tangent bundle, and
the compatibility proof saying the connection is metric-compatible with the
metric at each time. Smoothness and Ricci-flow evolution remain separate
predicate interfaces.
-/

namespace RicciFlower
namespace Realized

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

/-- A realized time-dependent metric and connection.

It does not assert that the connection is torsion-free, that the family is
smooth in time, or that it solves Ricci flow.  It does assert the basic
geometric compatibility between the stored metric and connection. -/
structure RealizedMetricFamily (Time : Type*) where
  metric : Time -> SmoothRiemannianMetric I M
  connection : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  metricCompatible : forall t : Time,
    RicciFlower.Connection.IsMetricCompatible (I := I) (connection t) (metric t)

/-- A realized metric family over a concrete real time interval.

The functions are defined on all real times, but later predicates only require
the Ricci-flow data on the interval's carrier or regular subdomain. -/
structure RealizedMetricFamilyOn (D : RealTimeInterval) where
  metric : Real -> SmoothRiemannianMetric I M
  connection : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _)
  metricCompatible : forall t : RealTimeInterval.FlowTime D,
    RicciFlower.Connection.IsMetricCompatible (I := I)
      (connection (t : Real)) (metric (t : Real))

namespace RealizedMetricFamily

@[simp] theorem metric_mk
    (metric : Time -> SmoothRiemannianMetric I M)
    (connection : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (metricCompatible : forall t : Time,
      RicciFlower.Connection.IsMetricCompatible (I := I) (connection t) (metric t))
    (t : Time) :
    (RealizedMetricFamily.mk (I := I) (M := M) metric connection
      metricCompatible).metric t = metric t := by
  rfl

@[simp] theorem connection_mk
    (metric : Time -> SmoothRiemannianMetric I M)
    (connection : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (metricCompatible : forall t : Time,
      RicciFlower.Connection.IsMetricCompatible (I := I) (connection t) (metric t))
    (t : Time) :
    (RealizedMetricFamily.mk (I := I) (M := M) metric connection
      metricCompatible).connection t =
      connection t := by
  rfl

@[simp] theorem metricCompatible_mk
    (metric : Time -> SmoothRiemannianMetric I M)
    (connection : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (metricCompatible : forall t : Time,
      RicciFlower.Connection.IsMetricCompatible (I := I) (connection t) (metric t))
    (t : Time) :
    (RealizedMetricFamily.mk (I := I) (M := M) metric connection
      metricCompatible).metricCompatible t = metricCompatible t := by
  rfl

end RealizedMetricFamily

namespace RealizedMetricFamilyOn

/-- View an interval family as a family indexed by its flow-time subtype. -/
def toFlowTimeFamily
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) :
    RealizedMetricFamily (I := I) (M := M) (RealTimeInterval.FlowTime D) where
  metric := fun t => G.metric (t : Real)
  connection := fun t => G.connection (t : Real)
  metricCompatible := fun t => G.metricCompatible t

/-- View an interval family as a family indexed by regular times. -/
def toRegularTimeFamily
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) :
    RealizedMetricFamily (I := I) (M := M) (RealTimeInterval.RegularTime D) where
  metric := fun t => G.metric (t : Real)
  connection := fun t => G.connection (t : Real)
  metricCompatible := fun t => G.metricCompatible (RealTimeInterval.regularToFlow t)

/-- Metric at a flow time. -/
def metricAt
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    SmoothRiemannianMetric I M :=
  G.metric (t : Real)

/-- Connection at a flow time. -/
def connectionAt
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    CovariantDerivative I E (TangentSpace I : M -> Type _) :=
  G.connection (t : Real)

@[simp] theorem metricAt_eq
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    G.metricAt t = G.metric (t : Real) := by
  rfl

@[simp] theorem connectionAt_eq
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    G.connectionAt t = G.connection (t : Real) := by
  rfl

/-- Metric compatibility of the connection and metric at a flow time. -/
theorem metricCompatibleAt
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.FlowTime D) :
    RicciFlower.Connection.IsMetricCompatible (I := I) (G.connectionAt t) (G.metricAt t) := by
  exact G.metricCompatible t

/-- Metric compatibility of the connection and metric at a regular time. -/
theorem metricCompatibleAt_regular
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : RealTimeInterval.RegularTime D) :
    RicciFlower.Connection.IsMetricCompatible (I := I)
      (G.connection (t : Real)) (G.metric (t : Real)) := by
  exact G.metricCompatible (RealTimeInterval.regularToFlow t)

end RealizedMetricFamilyOn

section FamilyCompatibility

/-- Metric compatibility for an interval metric family. -/
def IsMetricCompatibleFamilyOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop :=
  forall t : RealTimeInterval.FlowTime D,
    RicciFlower.Connection.IsMetricCompatible (I := I) (G.connectionAt t) (G.metricAt t)

/-- The metric-family field supplies interval metric compatibility. -/
theorem isMetricCompatibleFamilyOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) :
    IsMetricCompatibleFamilyOn (I := I) G :=
  fun t => G.metricCompatibleAt t

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
  RicciFlower.Connection.metric_compatible_apply (I := I) (hmc t) X Y Z hX hY hZ

end FamilyCompatibility

section TimeSmoothness

variable {A Time : Type*} [CommRing A] [Algebra Real A]

/-- Pointwise time-regularity of the metric coefficients.

This is intentionally a predicate, not a field of `RealizedMetricFamily`. -/
def MetricFamilySmoothInTime
    (td : TimeDerivativeData Real A Time) [TimeRegularFam td]
    (G : RealizedMetricFamily (I := I) (M := M) Time) : Prop :=
  forall (x : M) (X Y : TangentSpace I x),
    td.isSmoothFam (fun t : Time => (G.metric t).inner x X Y)

/-- Extract a metric coefficient's time smoothness from the predicate interface. -/
theorem metric_smooth_coeff_of_metricFamilySmoothInTime
    (td : TimeDerivativeData Real A Time) [TimeRegularFam td]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (hG : MetricFamilySmoothInTime td G)
    (x : M) (X Y : TangentSpace I x) :
    td.isSmoothFam (fun t : Time => (G.metric t).inner x X Y) :=
  hG x X Y

/-- The pointwise metric time derivative evaluated on fixed tangent vectors. -/
noncomputable def metricTimeDerivative
    (td : TimeDerivativeData Real A Time)
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (x : M) (X Y : TangentSpace I x) : Real :=
  td.dt_apply (fun s : Time => (G.metric s).inner x X Y) t

@[simp] theorem metricTimeDerivative_eq
    (td : TimeDerivativeData Real A Time)
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    metricTimeDerivative td G t x X Y =
      td.dt_apply (fun s : Time => (G.metric s).inner x X Y) t := by
  rfl

end TimeSmoothness

section IntervalSmoothness

/-- Time smoothness of metric coefficients over a concrete real interval. -/
def MetricFamilySmoothOn
    (D : RealTimeInterval)
    (G : RealizedMetricFamilyOn (I := I) (M := M) D) : Prop :=
  forall (x : M) (X Y : TangentSpace I x),
    ContDiffOn Real ⊤ (fun t : Real => (G.metric t).inner x X Y) D.carrier

/-- Extract a metric coefficient's interval time smoothness. -/
theorem metric_smooth_coeff_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (x : M) (X Y : TangentSpace I x) :
    ContDiffOn Real ⊤ (fun t : Real => (G.metric t).inner x X Y) D.carrier :=
  hG x X Y

/-- The scalar metric coefficient used in interval derivative statements. -/
noncomputable def metricCoeff
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (x : M) (X Y : TangentSpace I x) : Real -> Real :=
  fun t => (G.metric t).inner x X Y

@[simp] theorem metricCoeff_eq
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (x : M) (X Y : TangentSpace I x) (t : Real) :
    metricCoeff G x X Y t = (G.metric t).inner x X Y := by
  rfl

end IntervalSmoothness

end Realized
end RicciFlower
