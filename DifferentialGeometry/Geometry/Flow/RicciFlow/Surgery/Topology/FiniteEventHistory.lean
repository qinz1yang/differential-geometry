import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCapPreservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

variable {n : ℕ} (time : Fin (n + 1) → ℝ) (htime : StrictMono time) (hzero : time 0 = 0)
  (stage : Fin (n + 1) → OrientedThreeStage.{u}) (metric : (j : Fin (n + 1)) → (stage j).Metric)
  (event : (j : Fin n) → MetricCutCapEvent (stage j.castSucc) (stage j.succ)
    (time j.castSucc) (time j.succ))
  (hinitial : ∀ j, (event j).incoming.flow.base.metric (time j.castSucc) = metric j.castSucc)
  (houtput : ∀ j, (event j).outputMetric = metric j.succ)
  (hOld : ∀ j, (event j).old = (event j).transition.trace.retainedCore)

def ofEvents : RetainedCoreHistory.{u} where
  horizon := time (Fin.last n)
  horizon_nonneg := hzero ▸ htime.monotone (Fin.zero_le _)
  eventCount := n
  time := time
  time_strictMono := htime
  time_zero := hzero
  time_le_horizon := le_rfl
  stage := stage
  initialMetric := metric
  coreEvent j := (event j).toRetainedCoreEvent (hOld j)
  event_initial := hinitial
  event_output := houtput
  finalSlab h := False.elim (lt_irrefl _ h)
  final_initial h := False.elim (lt_irrefl _ h)

def ofEventsInitialIdentification :
    InitialIdentification (stage 0) (metric 0)
      (ofEvents time htime hzero stage metric event hinitial houtput hOld).toHistory :=
  InitialIdentification.ofStageZero (InitialIdentification.atZero (stage 0) (metric 0))
    rfl HEq.rfl

@[simp] theorem ofEvents_eventCount :
    (ofEvents time htime hzero stage metric event hinitial houtput hOld).eventCount = n := rfl

@[simp] theorem ofEvents_time (j : Fin (n + 1)) :
    (ofEvents time htime hzero stage metric event hinitial houtput hOld).time j = time j := rfl

@[simp] theorem ofEvents_stage (j : Fin (n + 1)) :
    (ofEvents time htime hzero stage metric event hinitial houtput hOld).stage j = stage j := rfl

@[simp] theorem ofEvents_initialMetric (j : Fin (n + 1)) :
    (ofEvents time htime hzero stage metric event hinitial houtput hOld).initialMetric j =
      metric j := rfl

@[simp] theorem ofEvents_coreEvent (j : Fin n) :
    (ofEvents time htime hzero stage metric event hinitial houtput hOld).coreEvent j =
      (event j).toRetainedCoreEvent (hOld j) := rfl

theorem ofEvents_regularCrossing_iff (j : Fin n)
    (p : (stage j.castSucc).Carrier) (q : (stage j.succ).Carrier) :
    MetricCutCapEvent.RegularCrossing
      ((ofEvents time htime hzero stage metric event hinitial houtput hOld).toHistory.event j)
      p q ↔ (event j).RegularCrossing p q :=
  (event j).regularCrossing_toRetainedCoreEvent_iff (hOld j) p q

theorem ofEvents_cap_scalar_lower_bound {c b B : ℝ}
    (hcap : ∀ j : Fin n, time j.succ ∈ Ioc c b →
      ∀ x ∈ (event j).capRegion, B ≤ metricScalarAt (event j).outputMetric x) :
    let H := ofEvents time htime hzero stage metric event hinitial houtput hOld
    ∀ j : Fin H.eventCount, H.time j.succ ∈ Ioc c b →
      ∀ x ∈ (H.toHistory.event j).capRegion,
        B ≤ metricScalarAt (H.toHistory.event j).outputMetric x := hcap

theorem ofEvents_cap_scalar_lower_bound_of_scale_le {c b Q : ℝ}
    (scale : Fin n → ℝ)
    (hscale : ∀ j : Fin n, time j.succ ∈ Ioc c b → 8 * Q ≤ scale j)
    (hcap : ∀ j : Fin n, time j.succ ∈ Ioc c b →
      ∀ x ∈ (event j).capRegion, scale j / 4 ≤ metricScalarAt (event j).outputMetric x) :
    let H := ofEvents time htime hzero stage metric event hinitial houtput hOld
    ∀ j : Fin H.eventCount, H.time j.succ ∈ Ioc c b →
      ∀ x ∈ (H.toHistory.event j).capRegion,
        2 * Q ≤ metricScalarAt (H.toHistory.event j).outputMetric x := by
  intro H j hj x hx
  have hlower := hcap j hj x hx
  have hs := hscale j hj
  change 2 * Q ≤ metricScalarAt (event j).outputMetric x
  linarith

theorem ofEvents_exists_backwardPointTrace
    (i first : Fin n) (hle : first.castSucc ≤ i.castSucc)
    (x : (event i).incoming.terminalRegularOpen) {q Q c b : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hqQ : q ≤ Q)
    (hscalar : metricScalarAt (event i).terminal.metric x ≤ (3 / 2 : ℝ) * Q)
    (hc : c ∈ Ico (time first.castSucc) (time first.succ))
    (htimeBudget : 6 * C * (time i.succ - c) * Q ≤ 1) (hib : time i.castSucc ≤ b)
    (hderiv : ∀ j : Fin n, first.castSucc ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (stage j.castSucc).Carrier, ∀ t ∈ Ioo (time j.castSucc) (time j.succ),
      q < (event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (event j).incoming.flow.scalar t y ^ 2)
    (scale : Fin n → ℝ)
    (hscale : ∀ j : Fin n, time j.succ ∈ Ioc c b → 8 * Q ≤ scale j)
    (hcap : ∀ j : Fin n, time j.succ ∈ Ioc c b →
      ∀ y ∈ (event j).capRegion, scale j / 4 ≤ metricScalarAt (event j).outputMetric y) :
    let H := ofEvents time htime hzero stage metric event hinitial houtput hOld
    ∃ A : BackwardPointTrace H.toHistory first.castSucc i.castSucc hle x.val,
      ∀ (j : Fin n) (hf : first.castSucc ≤ j.castSucc) (hl : j.castSucc ≤ i.castSucc),
        ∀ t ∈ Ico (time j.castSucc) (time j.succ), c ≤ t →
          (event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ 2 * Q := by
  intro H
  have hQ : 0 < Q := hq.trans_le hqQ
  have hbudget : C * (time i.succ - c) ≤ ((3 / 2 : ℝ) * Q)⁻¹ - (2 * Q)⁻¹ := by
    have he : ((3 / 2 : ℝ) * Q)⁻¹ - (2 * Q)⁻¹ = (6 * Q)⁻¹ := by field_simp; ring
    rw [he, inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 6 * Q)).mpr
    nlinarith
  exact H.exists_backwardPointTrace_on_time_window i first hle x hq (by linarith)
    (by linarith) hscalar hc hbudget hib hderiv
    (ofEvents_cap_scalar_lower_bound_of_scale_le time htime hzero stage metric event
      hinitial houtput hOld scale hscale hcap)

theorem ofEvents_exists_restart {c b B : ℝ}
    (hcap : ∀ j : Fin n, time j.succ ∈ Ioc c b →
      ∀ x ∈ (event j).capRegion, B ≤ metricScalarAt (event j).outputMetric x) :
    let H := ofEvents time htime hzero stage metric event hinitial houtput hOld
    ∃ K : RetainedCoreHistory.{u}, H.toHistory.IsPrefixOf K.toHistory ∧
      time (Fin.last n) < K.horizon ∧ ∃ hn : K.eventCount = n,
      (∀ j : Fin (K.eventCount + 1), K.time j = time (Fin.cast (congrArg (· + 1) hn) j)) ∧
      (∀ j : Fin K.eventCount,
        HEq (K.coreEvent j) ((event (Fin.cast hn j)).toRetainedCoreEvent (hOld _))) ∧
      ∀ j : Fin K.eventCount, K.time j.succ ∈ Ioc c b →
        ∀ x ∈ (K.toHistory.event j).capRegion,
          B ≤ metricScalarAt (K.toHistory.event j).outputMetric x := by
  intro H
  obtain ⟨T, hT, S, hS⟩ := exists_closedSlab_of_metric
    (H.stage (Fin.last H.eventCount)) (H.initialMetric (Fin.last H.eventCount))
    (H.time (Fin.last H.eventCount))
  let K := H.extendHorizon T hT.le S hS
  refine ⟨K,H.extendHorizon_isPrefixOf_of_time_eq_horizon T hT.le S hS rfl,hT,rfl,?_,?_,?_⟩
  · intro j
    rfl
  · intro j
    exact HEq.rfl
  · exact hcap

theorem ofEvents_append_samePresentation
    (time : Fin (n + 2) → ℝ) (htime : StrictMono time) (hzero : time 0 = 0)
    (stage : Fin (n + 2) → OrientedThreeStage.{u})
    (metric : (j : Fin (n + 2)) → (stage j).Metric)
    (event : (j : Fin (n + 1)) → MetricCutCapEvent (stage j.castSucc) (stage j.succ)
      (time j.castSucc) (time j.succ))
    (hinitial : ∀ j, (event j).incoming.flow.base.metric (time j.castSucc) = metric j.castSucc)
    (houtput : ∀ j, (event j).outputMetric = metric j.succ)
    (hOld : ∀ j, (event j).old = (event j).transition.trace.retainedCore) :
    let H := ofEvents (fun k => time k.castSucc) (htime.comp Fin.strictMono_castSucc)
      hzero (fun k => stage k.castSucc) (fun k => metric k.castSucc)
      (fun k => event k.castSucc) (fun k => hinitial k.castSucc)
      (fun k => houtput k.castSucc) (fun k => hOld k.castSucc)
    (H.appendEvent (htime (Fin.last n).castSucc_lt_succ)
      ((event (Fin.last n)).toRetainedCoreEvent (hOld (Fin.last n)))
      (hinitial (Fin.last n))).toHistory.SamePresentation
        (ofEvents time htime hzero stage metric event hinitial houtput hOld).toHistory := by
  intro H
  let E := (event (Fin.last n)).toRetainedCoreEvent (hOld (Fin.last n))
  let K := H.appendEvent (htime (Fin.last n).castSucc_lt_succ) E (hinitial (Fin.last n))
  let F := ofEvents time htime hzero stage metric event hinitial houtput hOld
  have ht (j : Fin (n + 2)) : K.time j = F.time j := by
    refine Fin.lastCases ?_ (fun k => ?_) j
    · exact H.appendEvent_time_last _ E _
    · exact H.appendEvent_time_castSucc _ E _ k
  have hp (j : Fin (n + 2)) : K.stage j = F.stage j := by
    refine Fin.lastCases ?_ (fun k => ?_) j
    · exact H.appendEvent_stage_last _ E _
    · exact H.appendEvent_stage_castSucc _ E _ k
  have hg (j : Fin (n + 2)) : HEq (K.initialMetric j) (F.initialMetric j) := by
    refine Fin.lastCases ?_ (fun k => ?_) j
    · exact (H.appendEvent_initialMetric_last_heq _ E _).trans
        (heq_of_eq (houtput (Fin.last n)))
    · exact H.appendEvent_initialMetric_castSucc_heq _ E _ k
  have hevent (j : Fin (n + 1)) : (K.toHistory.event j).SamePresentation (F.toHistory.event j) := by
    have hsp := H.appendEvent_toHistory_samePresentation
      (htime (Fin.last n).castSucc_lt_succ) E (hinitial (Fin.last n))
    apply (hsp.event_eq j).trans
    refine Fin.lastCases ?_ (fun k => ?_) j
    · exact H.toHistory.appendEvent_event_last_samePresentation _ E.toMetricCutCapEvent _
    · exact H.toHistory.appendEvent_event_castSucc_samePresentation _ E.toMetricCutCapEvent _ k
  refine {
    horizon_eq := rfl
    count_eq := rfl
    time_eq := ht
    stage_eq := hp
    initialMetric_heq := hg
    event_eq := hevent
    metric_heq := ?_ }
  intro j t hj
  change HEq (K.toHistory.stageMetric j t) (F.toHistory.stageMetric j t)
  revert hj
  refine Fin.lastCases ?_ (fun k => ?_) j
  · intro hj
    have hKend : K.time (Fin.last (n + 1)) = K.horizon := H.appendEvent_time_last _ E _
    have hFend : F.time (Fin.last (n + 1)) = F.horizon := rfl
    exact (heq_of_eq (ObservedHistory.stageMetric_last_of_le
      (H := K.toHistory) (le_of_eq hKend.symm) t)).trans
        ((hg (Fin.last (n + 1))).trans (heq_of_eq (ObservedHistory.stageMetric_last_of_le
          (H := F.toHistory) (le_of_eq hFend.symm) t)).symm)
  · intro hj
    exact (heq_of_eq (ObservedHistory.stageMetric_castSucc_apply (H := K.toHistory) k t)).trans
      (((hevent k).incomingMetric_heq t (by
        simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using hj)).trans
        (heq_of_eq (ObservedHistory.stageMetric_castSucc_apply (H := F.toHistory) k t)).symm)

theorem ofEvents_prefix
    (time : Fin (n + 2) → ℝ) (htime : StrictMono time) (hzero : time 0 = 0)
    (stage : Fin (n + 2) → OrientedThreeStage.{u})
    (metric : (j : Fin (n + 2)) → (stage j).Metric)
    (event : (j : Fin (n + 1)) → MetricCutCapEvent (stage j.castSucc) (stage j.succ)
      (time j.castSucc) (time j.succ))
    (hinitial : ∀ j, (event j).incoming.flow.base.metric (time j.castSucc) = metric j.castSucc)
    (houtput : ∀ j, (event j).outputMetric = metric j.succ)
    (hOld : ∀ j, (event j).old = (event j).transition.trace.retainedCore) :
    let H := ofEvents (fun k => time k.castSucc) (htime.comp Fin.strictMono_castSucc)
      hzero (fun k => stage k.castSucc) (fun k => metric k.castSucc)
      (fun k => event k.castSucc) (fun k => hinitial k.castSucc)
      (fun k => houtput k.castSucc) (fun k => hOld k.castSucc)
    H.toHistory.IsPrefixOf
      (ofEvents time htime hzero stage metric event hinitial houtput hOld).toHistory := by
  intro H
  let E := (event (Fin.last n)).toRetainedCoreEvent (hOld (Fin.last n))
  have hprefix := H.appendEvent_isPrefixOf (htime (Fin.last n).castSucc_lt_succ) E
    (hinitial (Fin.last n)) (htime (Fin.last n).castSucc_lt_succ)
    (H.appendEventCompatible_of_time_eq_horizon E rfl)
  let K := H.appendEvent (htime (Fin.last n).castSucc_lt_succ) E (hinitial (Fin.last n))
  let F := ofEvents time htime hzero stage metric event hinitial houtput hOld
  have hsame := ofEvents_append_samePresentation time htime hzero stage metric event
    hinitial houtput hOld
  have hKF : K.toHistory.IsPrefixOf F.toHistory := by
    refine ⟨le_of_eq hsame.horizon_eq, ?_⟩
    have ht : (⟨K.horizon, K.horizon_nonneg, le_of_eq hsame.horizon_eq⟩ :
        Icc (0 : ℝ) F.horizon) = ⟨F.horizon, F.horizon_nonneg, le_rfl⟩ :=
      Subtype.ext hsame.horizon_eq
    rw [ht]
    exact F.toHistory.restrict_self.trans hsame.symm
  exact hprefix.trans hKF

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
