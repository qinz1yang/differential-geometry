import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap
import DifferentialGeometry.Geometry.Metric.Comparison.IsometricBalls

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_survivor_ambient_ball_images
    (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old))
    (p : E.incoming.terminalRegularOpen) {R : ℝ}
    (hcpt : IsCompact (riemannianClosedBallOf E.terminal.metric p R))
    (hball : riemannianClosedBallOf E.terminal.metric p R ⊆ W) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        E.incoming.terminalRegularOpen Q.Carrier ∞,
      F.source = W ∧
      (∀ x ∈ W, E.RegularCrossing x.val (F x)) ∧
      (∀ z : E.old, E.oldTerminal z ∈ W → F (E.oldTerminal z) = E.oldOutput z) ∧
      (∀ z : E.old, E.oldTerminal z ∈ W →
        E.transition.trace.presentation (E.transition.trace.capping.coreInclusion z.val) =
          Sum.inl (F (E.oldTerminal z))) ∧
      (∀ x ∈ W, ∀ v w : TangentSpace ThreeModel x,
        E.outputMetric.inner (F x) (mfderiv ThreeModel ThreeModel (F : _ → _) x v)
          (mfderiv ThreeModel ThreeModel (F : _ → _) x w) =
          E.terminal.metric.inner x v w) ∧
      (∀ r : ℝ, 0 ≤ r → r < R →
        (F : E.incoming.terminalRegularOpen → Q.Carrier) ''
            riemannianClosedBallOf E.terminal.metric p r =
          riemannianClosedBallOf E.outputMetric (F p) r) ∧
      (∀ r : ℝ, 0 < r → r < R →
        (F : E.incoming.terminalRegularOpen → Q.Carrier) ''
            riemannianBallOf E.terminal.metric p r =
          riemannianBallOf E.outputMetric (F p) r) ∧
      ∀ r : ℝ, 0 ≤ r → r < R →
        IsCompact (riemannianClosedBallOf E.outputMetric (F p) r) := by
  have hp : p ∈ W := hball (by
    change riemannianEDistOf E.terminal.metric p p ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact bot_le)
  obtain ⟨F, hsource, hcross, hold, hmetric⟩ :=
    E.exists_survivor_partialDiffeomorph W ⟨p, hp⟩ hW
  have hsourceball : riemannianClosedBallOf E.terminal.metric p R ⊆ F.source := by
    rw [hsource]
    exact hball
  have hmetricball (x) (hx : x ∈ riemannianClosedBallOf E.terminal.metric p R)
      (v : TangentSpace ThreeModel x) := hmetric x (hball hx) v v
  have hclosed (r : ℝ) (hr : 0 ≤ r) (hrR : r < R) :=
    DifferentialGeometry.PartialDiffeomorph.image_riemannianClosedBall_eq_of_isometric_on_compact_ball
      E.terminal.metric E.outputMetric F p hr hrR hcpt hsourceball hmetricball
  refine ⟨F, hsource, hcross, hold, ?_, hmetric, hclosed, ?_, ?_⟩
  · intro z hz
    rw [hold z hz]
    exact E.oldOutput_eq z
  · intro r hr hrR
    exact DifferentialGeometry.PartialDiffeomorph.image_riemannianBall_eq_of_isometric_on_compact_ball
      E.terminal.metric E.outputMetric F p hr hrR hcpt hsourceball hmetricball
  · intro r hr hrR
    rw [← hclosed r hr hrR]
    have hsub := riemannianClosedBallOf_mono E.terminal.metric p hrR.le
    have hclosedball : IsClosed (riemannianClosedBallOf E.terminal.metric p r) :=
      isClosed_le (continuous_riemannianEDist E.terminal.metric p) continuous_const
    exact (hcpt.of_isClosed_subset hclosedball hsub).image_of_continuousOn
      (F.contMDiffOn_toFun.continuousOn.mono (hsub.trans hsourceball))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
