import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreMetricEvent
import DifferentialGeometry.Geometry.Metric.Distance.Basic

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- Every truncated distance on the original terminal regular metric extends to
one scalar on this actual output, with a common physical Lipschitz constant.
The predicate depends on the event, independently of any subsequent record choice. -/
def MetricCutCapEvent.HasUniformDistanceScalar
    {P Q : OrientedThreeStage.{u}} {a s : ℝ}
    (E : MetricCutCapEvent P Q a s) (C : ℝ≥0) : Prop :=
  ∀ (p : E.incoming.terminalRegularOpen) (N : ℝ≥0),
    ∃ G : Q.Carrier → ℝ,
      (∀ z : E.old, G (E.oldOutput z) =
        (min (riemannianEDistOf E.terminal.metric (E.oldTerminal z) p)
          (N : ℝ≥0∞)).toReal) ∧
      ∀ y z : Q.Carrier,
        edist (G y) (G z) ≤ (C : ℝ≥0∞) * riemannianEDistOf E.outputMetric y z

private theorem distanceScalar_toRetainedCoreEvent
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {C : ℝ≥0}
    (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hscalar : E.HasUniformDistanceScalar C) :
    (E.toRetainedCoreEvent hOld).toMetricCutCapEvent.HasUniformDistanceScalar C := by
  intro p N
  obtain ⟨G, hG, hLip⟩ := hscalar p N
  refine ⟨G, ?_, hLip⟩
  intro z
  exact hG (E.retainedOldDiffeomorph hOld z)

private theorem distanceScalar_of_retainedEvent_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ} {C : ℝ≥0}
    (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (E' : RetainedCoreEvent P' Q' a' s')
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s)
    (hE : HEq E' (E.toRetainedCoreEvent hOld))
    (hscalar : E.HasUniformDistanceScalar C) :
    E'.toMetricCutCapEvent.HasUniformDistanceScalar C := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact distanceScalar_toRetainedCoreEvent E hOld hscalar

/-- Transport the proved event property to the actual selected history event.
The original retained-point domains are identified by the retained-old
isomorphism; the scalar and both physical metrics are preserved. -/
theorem MetricCutCapEvent.HasUniformDistanceScalar.of_coreEvent_heq
    {P Q : OrientedThreeStage.{u}} {H : RetainedCoreHistory.{u}} {i : Fin H.eventCount}
    {a s : ℝ} {C : ℝ≥0} (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hP : H.stage i.castSucc = P) (hQ : H.stage i.succ = Q)
    (ha : H.time i.castSucc = a) (hs : H.time i.succ = s)
    (hE : HEq (H.coreEvent i) (E.toRetainedCoreEvent hOld))
    (hscalar : E.HasUniformDistanceScalar C) :
    (H.toHistory.event i).HasUniformDistanceScalar C :=
  distanceScalar_of_retainedEvent_heq E hOld (H.coreEvent i) hP hQ ha hs hE hscalar

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
