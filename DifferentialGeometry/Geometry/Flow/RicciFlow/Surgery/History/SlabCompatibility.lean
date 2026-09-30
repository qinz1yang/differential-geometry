import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabUniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem singular_time_gt_closed_end {P : OrientedThreeStage.{u}} {a b s : ℝ}
    (F : P.ClosedSlab a b) (G : P.IncomingSlab a s)
    (hi : G.flow.base.metric a = F.flow.base.metric a)
    (hs : G.SingularEndpoint) : b < s := by
  by_contra hn
  have hsb : s ≤ b := le_of_not_gt hn
  let A := F.restrictIncoming le_rfl F.lt le_rfl
  have heq := G.metric_eq_on_Ico_of_initial A hi
  obtain ⟨K,hK,hbound⟩ := F.curvature_bound P
  obtain ⟨t,ht,x,hx⟩ := hs (K+1) (by linarith) a ⟨le_rfl,G.lt⟩
  have hmetric : G.flow.base.metric t = F.flow.base.metric t :=
    heq t ⟨ht.1.le, lt_min ht.2 (ht.2.trans_le hsb)⟩
  have hnorm : G.riemannNorm t x =
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
        (F.flow.base.metric t) x 4 (F.flow.base.rm04 t x)) := by
    change Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
      (G.flow.base.metric t) x 4 (metricRm04 (G.flow.base.metric t) x)) = _
    rw [hmetric]
    rfl
  rw [hnorm] at hx
  have hb := hbound t ⟨ht.1.le,ht.2.le.trans hsb⟩ x
  linarith

theorem closed_slabs_agree {P : OrientedThreeStage.{u}} {a b c : ℝ}
    (F : P.ClosedSlab a b) (G : P.ClosedSlab a c)
    (hi : F.flow.base.metric a = G.flow.base.metric a) :
    ∀ t ∈ Icc a (min b c), F.flow.base.metric t = G.flow.base.metric t := by
  have hab : a < min b c := lt_min F.lt G.lt
  have heq := (F.restrictIncoming le_rfl F.lt le_rfl).metric_eq_on_Ico_of_initial
    (G.restrictIncoming le_rfl G.lt le_rfl) hi
  intro t ht
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hF := (F.equation.smoothMetric.coeff_cont x v w).mono
    (show Icc a (min b c) ⊆ Icc a b from fun _ hz => ⟨hz.1,hz.2.trans (min_le_left _ _)⟩)
  have hG := (G.equation.smoothMetric.coeff_cont x v w).mono
    (show Icc a (min b c) ⊆ Icc a c from fun _ hz => ⟨hz.1,hz.2.trans (min_le_right _ _)⟩)
  have hcoeff : Set.EqOn (fun r => (F.flow.base.metric r).inner x v w)
      (fun r => (G.flow.base.metric r).inner x v w) (Ico a (min b c)) := by
    intro r hr
    exact congrArg (fun g : P.Metric => g.inner x v w) (heq r hr)
  exact hcoeff.of_subset_closure hF hG Ico_subset_Icc_self
    (by rw [closure_Ico hab.ne]) ht

theorem incoming_agrees_with_closed_tail {P : OrientedThreeStage.{u}} {a b s : ℝ}
    (F : P.ClosedSlab a b) (G : P.IncomingSlab a s)
    (hi : G.flow.base.metric a = F.flow.base.metric a) (hbs : b < s) :
    ∀ t ∈ Icc a b, G.flow.base.metric t = F.flow.base.metric t := by
  intro t ht
  exact closed_slabs_agree (G.closedPrefix b F.lt hbs) F hi t
    ⟨ht.1,le_min ht.2 ht.2⟩

theorem actual_singular_event_after_horizon {Q : OrientedThreeStage.{u}}
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hi : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hs : E.incoming.SingularEndpoint) : H.horizon < s := by
  rcases H.time_le_horizon.lt_or_eq with ht | ht
  · exact singular_time_gt_closed_end (H.finalSlab ht) E.incoming
      (hi.trans (H.final_initial ht).symm) hs
  · exact ht ▸ E.incoming.lt

theorem actual_singular_event_compatible {Q : OrientedThreeStage.{u}}
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hi : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hs : E.incoming.SingularEndpoint) : H.appendEventCompatible E := by
  intro ht t htime
  exact incoming_agrees_with_closed_tail (H.finalSlab ht) E.incoming
    (hi.trans (H.final_initial ht).symm)
    (actual_singular_event_after_horizon H E hi hs) t htime

theorem actual_singular_event_preserves_prefix {Q : OrientedThreeStage.{u}}
    (H : RetainedCoreHistory.{u}) {s : ℝ}
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hi : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hs : E.incoming.SingularEndpoint) :
    H.toHistory.IsPrefixOf (H.appendEvent E.incoming.lt E hi).toHistory :=
  H.appendEvent_isPrefixOf E.incoming.lt E hi
    (actual_singular_event_after_horizon H E hi hs)
    (actual_singular_event_compatible H E hi hs)

theorem actual_closed_extension_compatible
    (H : RetainedCoreHistory.{u}) {T : ℝ} (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab
      (H.time (Fin.last H.eventCount)) T)
    (hi : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) : H.extendHorizonCompatible T S := by
  rcases H.time_le_horizon.lt_or_eq with ht | ht
  · intro t htime
    rw [ObservedHistory.stageMetric_last_of_lt (H := H.toHistory) (h := ht)]
    exact closed_slabs_agree S (H.finalSlab ht)
      (hi.trans (H.final_initial ht).symm) t
      ⟨htime.1,le_min (htime.2.trans hT) htime.2⟩
  · exact H.extendHorizonCompatible_of_time_eq_horizon T S hi ht

theorem actual_closed_extension_preserves_prefix
    (H : RetainedCoreHistory.{u}) {T : ℝ} (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab
      (H.time (Fin.last H.eventCount)) T)
    (hi : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    H.toHistory.IsPrefixOf (H.extendHorizon T hT S hi).toHistory :=
  H.extendHorizon_isPrefixOf T hT S hi (actual_closed_extension_compatible H hT S hi)

end GC.GeneralFlow
