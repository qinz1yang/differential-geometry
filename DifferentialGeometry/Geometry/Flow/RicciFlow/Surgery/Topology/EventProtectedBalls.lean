import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventSurvivorMap
import DifferentialGeometry.Geometry.Metric.Comparison.IsometricBalls
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Topology.SigmaCompactOpen

noncomputable section

open Set Manifold MeasureTheory
open DifferentialGeometry.Integral.Measure
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

private local instance : MeasurableSpace E.incoming.terminalRegularOpen :=
  borel E.incoming.terminalRegularOpen
private local instance : BorelSpace E.incoming.terminalRegularOpen := ⟨rfl⟩
private local instance : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel E.incoming.terminalRegularOpen.isOpen)

theorem exists_survivor_ambient_ball_volume_eq
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
      (∀ r : ℝ, 0 ≤ r → r < R →
        IsCompact (riemannianClosedBallOf E.outputMetric (F p) r)) ∧
      ∀ r : ℝ, 0 < r → r < R →
        riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
          (riemannianBallOf E.outputMetric (F p) r) =
        riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
          (riemannianBallOf E.terminal.metric p r) := by
  obtain ⟨F, hsource, hcross, hold, hpresentation, hmetric, hclosed, hopen, hcompact⟩ :=
    E.exists_survivor_ambient_ball_images W hW p hcpt hball
  refine ⟨F, hsource, hcross, hold, hpresentation, hmetric, hclosed, hopen, hcompact, ?_⟩
  intro r hr hrR
  rw [← hopen r hr hrR]
  symm
  let F₁ : PartialDiffeomorph ThreeModel ThreeModel E.incoming.terminalRegularOpen Q.Carrier 1 :=
    { F.toPartialEquiv with
      open_source := F.open_source
      open_target := F.open_target
      contMDiffOn_toFun := F.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := F.contMDiffOn_invFun.of_le (by norm_num) }
  apply riemannianVolumeMeasure_image_of_partialIsometry E.terminal.metric E.outputMetric F₁
  · intro x hx v w
    change x ∈ F.source at hx
    have hxW : x ∈ W := by
      change x ∈ (W : Set E.incoming.terminalRegularOpen)
      rw [← hsource]
      exact hx
    exact (hmetric x hxW v w).symm
  · exact (isOpen_lt (continuous_riemannianEDist E.terminal.metric p) continuous_const).measurableSet
  · change riemannianBallOf E.terminal.metric p r ⊆ F.source
    rw [hsource]
    intro x hx
    exact hball (hx.le.trans (ENNReal.ofReal_le_ofReal hrR.le))

theorem riemannianVolumeMeasure_ball_eq_of_regularCrossing
    (p : E.incoming.terminalRegularOpen) (q : Q.Carrier)
    (hcross : E.RegularCrossing p.val q) {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf E.terminal.metric p R))
    (hprotected : ∀ x ∈ riemannianClosedBallOf E.terminal.metric p R,
      x.val ∈ interior (Subtype.val '' E.old)) :
    riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
      (riemannianBallOf E.outputMetric q r) =
    riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
      (riemannianBallOf E.terminal.metric p r) := by
  let W : TopologicalSpace.Opens E.incoming.terminalRegularOpen :=
    ⟨Subtype.val ⁻¹' interior (Subtype.val '' E.old), isOpen_interior.preimage continuous_subtype_val⟩
  have hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old) := fun _ hx => hx
  obtain ⟨F, _, hFcross, _, _, _, _, _, _, hvolume⟩ :=
    E.exists_survivor_ambient_ball_volume_eq W hW p hcpt hprotected
  have hp : p ∈ W := hprotected p (by
    change riemannianEDistOf E.terminal.metric p p ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact bot_le)
  have heq : F p = q := E.regularCrossing_right_unique (hFcross p hp) hcross
  simpa only [heq] using hvolume r hr hrR

theorem volume_ball_lower_bound_of_regularCrossing
    (p : E.incoming.terminalRegularOpen) (q : Q.Carrier)
    (hcross : E.RegularCrossing p.val q) {R r κ : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcpt : IsCompact (riemannianClosedBallOf E.terminal.metric p R))
    (hprotected : ∀ x ∈ riemannianClosedBallOf E.terminal.metric p R,
      x.val ∈ interior (Subtype.val '' E.old))
    (hvolume : ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric
        (riemannianBallOf E.terminal.metric p r)) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric
        (riemannianBallOf E.outputMetric q r) := by
  rw [E.riemannianVolumeMeasure_ball_eq_of_regularCrossing p q hcross hr hrR hcpt hprotected]
  exact hvolume

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
