import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Analysis.Integration.Measure.RealizedMetricForMeasure
import DifferentialGeometry.Geometry.Metric.DistanceScaling

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Perelman no-local-collapsing statement interfaces

This file records the MSM135 Chapter 6 noncollapsing vocabulary without
asserting the hard global analytic theorem.  The canonical `FlowMetricBall` API
uses the actual time-slice metric, Riemannian volume measure, and canonical
curvature tensor.  The older arbitrary-numeric records remain below only as an
explicit legacy compatibility layer.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

universe u uE uH

open Bundle Tensor0SBundle MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

/-- A genuine geodesic ball in a time slice of a Ricci-flow candidate.

The time is a `FlowTime D` parameter, so interval membership is encoded by the
type.  The structure stores only the center and positive radius; its set,
volume, and curvature-scale predicates are derived from the flow. -/
structure FlowMetricBall (S : SolutionOn (I := I) (M := M) D)
    (time : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D) where
  center : M
  radius : Real
  radius_pos : 0 < radius

namespace FlowMetricBall

variable {S : SolutionOn (I := I) (M := M) D}
variable {time : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D}

/-- The open ball with `B`'s center and radius, measured using the time-`t`
metric. -/
def setAt (B : FlowMetricBall S time) (t : Real) : Set M :=
  {x : M | DifferentialGeometry.riemannianEDistOf
    (I := I) (S.base.metric t) B.center x < ENNReal.ofReal B.radius}

/-- The flow metric ball at its distinguished time. -/
def set (B : FlowMetricBall S time) : Set M :=
  B.setAt (time : Real)

/-- The actual Riemannian volume of a flow metric ball. -/
def volume (B : FlowMetricBall S time) : ℝ≥0∞ :=
  DifferentialGeometry.Integral.Measure.volumeMeasureOn
    (I := I) (M := M) S.family time B.set

/-- The squared norm of the canonical lowered Riemann tensor of `S(t)`. -/
def rmNormSq (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) : Real :=
  Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)

/-- Curvature is controlled at scale `r` on the backward parabolic cylinder
based on the time-`B.time` ball.  Squared curvature is used, hence the
scale-invariant inequality `r⁴ |Rm|² ≤ 1`. -/
def IsRmControlled (B : FlowMetricBall S time) : Prop :=
  Set.Icc ((time : Real) - B.radius ^ 2) (time : Real) ⊆ D.carrier ∧
    ∀ t ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real), ∀ x ∈ B.setAt t,
      B.radius ^ 4 * rmNormSq S t x ≤ 1

/-- The actual volume lower bound defining `κ`-noncollapsing on one flow ball,
using the model dimension. -/
def IsKappaNoncollapsed (kappa : Real) (B : FlowMetricBall S time) : Prop :=
  0 < kappa ∧
    ENNReal.ofReal kappa * ENNReal.ofReal B.radius ^ Module.finrank Real E ≤ B.volume

/-- Actual set-theoretic nesting of flow metric balls at the same time. -/
def Nested (small large : FlowMetricBall S time) : Prop :=
  small.set ⊆ large.set

/-- Riemannian volume is monotone under genuine ball inclusion. -/
theorem volume_mono {small large : FlowMetricBall S time} (h : small.Nested large) :
    small.volume ≤ large.volume := by
  unfold volume
  exact measure_mono h

end FlowMetricBall

/-- `κ`-noncollapsing on every curvature-controlled flow ball below scale
`rho`. -/
def KappaNoncollapsedBelowScale
    (S : SolutionOn (I := I) (M := M) D) (kappa rho : Real) : Prop :=
  0 < rho ∧ ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D)
    (B : FlowMetricBall S t), B.radius ≤ rho →
    B.IsRmControlled → B.IsKappaNoncollapsed kappa

/-- The geometric no-local-collapsing conclusion below a fixed scale.  The
hard Perelman theorem is the future producer of this predicate. -/
def NoLocalCollapsing
    (S : SolutionOn (I := I) (M := M) D) (rho : Real) : Prop :=
  ∃ kappa : Real, 0 < kappa ∧ KappaNoncollapsedBelowScale S kappa rho

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
