import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCapPreservation

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent.PresentedStaticCap

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
  (S : E.PresentedStaticCap fixed D m ε b)

def window : C(standardCapWindow D, Q.Carrier) := S.inclusion.comp S.witness.window

theorem window_smooth : IsSmoothEmbedding ThreeModel ThreeModel ∞ S.window :=
  S.inclusion_smooth.comp S.witness.window_smooth (by simp)

theorem window_inner (x : standardCapWindow D) (v w : TangentSpace ThreeModel x) :
    S.witness.windowMetric.inner x v w = S.neck.scale *
      E.outputMetric.inner (S.window x)
        (mfderiv ThreeModel ThreeModel S.window x v)
        (mfderiv ThreeModel ThreeModel S.window x w) := by
  rw [S.witness.window_inner, S.inclusion_metric]
  change _ = S.neck.scale * E.outputMetric.inner _
    (mfderiv ThreeModel ThreeModel (S.inclusion ∘ S.witness.window) x v)
    (mfderiv ThreeModel ThreeModel (S.inclusion ∘ S.witness.window) x w)
  rw [mfderiv_comp x (S.inclusion_smooth.contMDiff.mdifferentiableAt (by simp))
    (S.witness.window_smooth.contMDiff.mdifferentiableAt (by simp))]
  rfl

def toRetained (hOld : E.old = E.transition.trace.retainedCore) :
    (E.toRetainedCoreEvent hOld).toMetricCutCapEvent.PresentedStaticCap fixed D m ε b where
  delta := S.delta
  order := S.order
  neck := S.neck
  witness := S.witness
  inclusion := S.inclusion
  inclusion_smooth := S.inclusion_smooth
  inclusion_metric := S.inclusion_metric
  cap_eq := S.cap_eq
  attaching_eq := S.attaching_eq
  retainedPoint := S.retainedPoint
  retained_point_eq := S.retained_point_eq
  retained_eq := S.retained_eq

@[simp] theorem toRetained_window (hOld : E.old = E.transition.trace.retainedCore) :
    (S.toRetained hOld).window = S.window := rfl

end MetricCutCapEvent.PresentedStaticCap

theorem MetricCutCapEvent.range_oldOutput_toRetainedCoreEvent
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    range (E.toRetainedCoreEvent hOld).toMetricCutCapEvent.oldOutput = range E.oldOutput := by
  let e := E.retainedOldDiffeomorph hOld
  change range (E.oldOutput ∘ e) = range E.oldOutput
  exact e.surjective.range_comp E.oldOutput

private theorem exists_static_family_of_retainedEvent_heq
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : MetricCutCapEvent P Q a s) (hOld : E.old = E.transition.trace.retainedCore)
    (E' : RetainedCoreEvent P' Q' a' s')
    (hP : P' = P) (hQ : Q' = Q) (ha : a' = a) (hs : s' = s)
    (hE : HEq E' (E.toRetainedCoreEvent hOld))
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b) :
    ∃ (e : E'.toMetricCutCapEvent.RetainedBoundaryIndex ≃ E.RetainedBoundaryIndex)
      (S' : ∀ b : E'.toMetricCutCapEvent.RetainedBoundaryIndex,
        E'.toMetricCutCapEvent.PresentedStaticCap fixed D m ε b),
      (∀ b, HEq b.val (e b).val) ∧
      (∀ b, HEq (S' b).neck (S (e b)).neck) ∧
      (∀ b, (S' b).neck.scale = (S (e b)).neck.scale) ∧
      (∀ b, HEq (S' b).witness (S (e b)).witness) ∧
      (∀ b, HEq (S' b).inclusion (S (e b)).inclusion) ∧
      (∀ b, HEq (S' b).window (S (e b)).window) ∧
      HEq E'.outputMetric E.outputMetric ∧
      HEq (range E'.toMetricCutCapEvent.oldOutput) (range E.oldOutput) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact ⟨Equiv.refl _, fun b => (S b).toRetained hOld,
    fun _ => HEq.rfl, fun _ => HEq.rfl, fun _ => rfl, fun _ => HEq.rfl, fun _ => HEq.rfl,
    fun _ => HEq.rfl, HEq.rfl, heq_of_eq (E.range_oldOutput_toRetainedCoreEvent hOld)⟩

private theorem exists_window_of_stage_metric_heq
    {P Q : OrientedThreeStage.{u}} (hP : P = Q)
    (gP : P.Metric) (gQ : Q.Metric) (hg : HEq gP gQ)
    {D q : ℝ} (g : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (J : C(standardCapWindow D, Q.Carrier))
    (hJ : IsSmoothEmbedding ThreeModel ThreeModel ∞ J)
    (hmetric : ∀ x v w, g.inner x v w = q * gQ.inner (J x)
      (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w)) :
    ∃ K : C(standardCapWindow D, P.Carrier), HEq K J ∧
      IsSmoothEmbedding ThreeModel ThreeModel ∞ K ∧
      ∀ x v w, g.inner x v w = q * gP.inner (K x)
        (mfderiv ThreeModel ThreeModel K x v) (mfderiv ThreeModel ThreeModel K x w) := by
  cases hP
  cases eq_of_heq hg
  exact ⟨J, HEq.rfl, hJ, hmetric⟩

theorem RetainedCoreHistory.exists_static_window_at_appendEvent
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
    (S : E.PresentedStaticCap fixed D m ε b) :
    let K := H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit
    ∃ J : C(standardCapWindow D, (K.stage (Fin.last K.eventCount)).Carrier),
      HEq J S.window ∧ IsSmoothEmbedding ThreeModel ThreeModel ∞ J ∧
      ∀ x v w, S.witness.windowMetric.inner x v w = S.neck.scale *
        (K.initialMetric (Fin.last K.eventCount)).inner (J x)
          (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w) := by
  exact exists_window_of_stage_metric_heq
    (H.appendEvent_stage_last E.incoming.lt (E.toRetainedCoreEvent hOld) hinit)
    _ E.outputMetric
    (H.appendEvent_initialMetric_last_heq E.incoming.lt (E.toRetainedCoreEvent hOld) hinit)
    S.witness.windowMetric S.window S.window_smooth S.window_inner

theorem RetainedCoreHistory.exists_static_cap_family_at_appendEvent
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
    (S : ∀ b : E.RetainedBoundaryIndex, E.PresentedStaticCap fixed D m ε b) :
    let K := H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit
    let i : Fin K.eventCount := Fin.last H.eventCount
    ∃ (e : (K.toHistory.event i).RetainedBoundaryIndex ≃ E.RetainedBoundaryIndex)
      (S' : ∀ b : (K.toHistory.event i).RetainedBoundaryIndex,
        (K.toHistory.event i).PresentedStaticCap fixed D m ε b),
      HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
      (∀ b, HEq b.val (e b).val) ∧
      (∀ b, HEq (S' b).neck (S (e b)).neck) ∧
      (∀ b, (S' b).neck.scale = (S (e b)).neck.scale) ∧
      (∀ b, HEq (S' b).witness (S (e b)).witness) ∧
      (∀ b, HEq (S' b).inclusion (S (e b)).inclusion) ∧
      (∀ b, HEq (S' b).window (S (e b)).window) ∧
      HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
      HEq (range (K.toHistory.event i).oldOutput) (range E.oldOutput) := by
  let F := E.toRetainedCoreEvent hOld
  let K := H.appendEvent E.incoming.lt F hinit
  let i : Fin K.eventCount := Fin.last H.eventCount
  have hE : HEq (K.coreEvent i) F := by
    change HEq ((H.appendEvent E.incoming.lt F hinit).coreEvent (Fin.last H.eventCount)) F
    refine (heq_of_eq (H.appendEvent_coreEvent_last E.incoming.lt F hinit)).trans ?_
    change HEq (H.extendCoreEventLast F) F
    unfold RetainedCoreHistory.extendCoreEventLast
    have ht {P₁ Q₁ P₂ Q₂ : OrientedThreeStage.{u}} {a₁ s₁ a₂ s₂ : ℝ}
        (hP : P₁ = P₂) (hQ : Q₁ = Q₂) (ha : a₁ = a₂) (hs : s₁ = s₂)
        (T : RetainedCoreEvent P₁ Q₁ a₁ s₁) :
        HEq (RetainedCoreEvent.transport hP hQ ha hs T) T := by
      cases hP
      cases hQ
      cases ha
      cases hs
      exact HEq.rfl
    exact ht _ _ _ _ _
  obtain ⟨e, S', hlabel, hneck, hscale, hwitness, hinclusion, hwindow, _, hold⟩ :=
    exists_static_family_of_retainedEvent_heq E hOld (K.coreEvent i)
      (H.appendEvent_stage_castSucc E.incoming.lt F hinit (Fin.last H.eventCount))
      (H.appendEvent_stage_last E.incoming.lt F hinit)
      (H.appendEvent_time_castSucc E.incoming.lt F hinit (Fin.last H.eventCount))
      (H.appendEvent_time_last E.incoming.lt F hinit) hE S
  exact ⟨e, S', hE, hlabel, hneck, hscale, hwitness, hinclusion, hwindow,
    H.appendEvent_initialMetric_last_heq E.incoming.lt F hinit, hold⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
