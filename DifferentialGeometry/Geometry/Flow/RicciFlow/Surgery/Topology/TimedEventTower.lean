import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerBookkeeping
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem closedPrefix_flow_metric {P : OrientedThreeStage.{u}} {a s b : ℝ}
    (G : P.IncomingSlab a s) (hab : a < b) (hbs : b < s) (τ : ℝ) :
    (G.closedPrefix b hab hbs).flow.base.metric τ = G.flow.base.metric τ := rfl

structure RetainedCoreTimedEventChain (P : OrientedThreeStage.{u}) (g : P.Metric) where
  time : ℕ → ℝ
  time_zero : time 0 = 0
  time_gt : ∀ n : ℕ, (n : ℝ) < time (n + 1)
  time_le : ∀ n : ℕ, time (n + 1) ≤ (n : ℝ) + 1
  stage : ℕ → OrientedThreeStage.{u}
  metric : (n : ℕ) → (stage n).Metric
  stage_zero : stage 0 = P
  metric_zero : HEq (metric 0) g
  event : (n : ℕ) → RetainedCoreEvent (stage n) (stage (n + 1)) (time n) (time (n + 1))
  event_initial : ∀ n : ℕ,
    (event n).toMetricCutCapEvent.incoming.flow.base.metric (time n) = metric n
  event_output : ∀ n : ℕ, (event n).toMetricCutCapEvent.outputMetric = metric (n + 1)

namespace RetainedCoreTimedEventChain

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (C : RetainedCoreTimedEventChain P g)

theorem time_lt_succ (n : ℕ) : C.time n < C.time (n + 1) := by
  rcases n with _ | n
  · rw [C.time_zero]
    simpa using C.time_gt 0
  · have h : C.time (n + 1) ≤ ((n + 1 : ℕ) : ℝ) := by
      push_cast
      exact C.time_le n
    exact h.trans_lt (C.time_gt (n + 1))

theorem time_strictMono : StrictMono C.time :=
  strictMono_nat_of_lt_succ C.time_lt_succ

theorem time_nonneg (n : ℕ) : 0 ≤ C.time n :=
  C.time_zero ▸ C.time_strictMono.monotone (Nat.zero_le n)

theorem time_le_index (n : ℕ) : C.time n ≤ (n : ℝ) := by
  rcases n with _ | n
  · rw [C.time_zero]
    norm_num
  · push_cast
    exact C.time_le n

end RetainedCoreTimedEventChain

namespace RetainedCoreHistory

private def attach (H : RetainedCoreHistory.{u}) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (h : H.time (Fin.last H.eventCount) < T) →
      (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : ∀ h, (S h).flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) : RetainedCoreHistory.{u} where
  horizon := T
  horizon_nonneg := H.horizon_nonneg.trans hT
  eventCount := H.eventCount
  time := H.time
  time_strictMono := H.time_strictMono
  time_zero := H.time_zero
  time_le_horizon := H.time_le_horizon.trans hT
  stage := H.stage
  initialMetric := H.initialMetric
  coreEvent := H.coreEvent
  event_initial := H.event_initial
  event_output := H.event_output
  finalSlab := S
  final_initial := hS

private theorem attach_isPrefixOf (H : RetainedCoreHistory.{u}) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (h : H.time (Fin.last H.eventCount) < T) →
      (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : ∀ h, (S h).flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (htime : H.time (Fin.last H.eventCount) = H.horizon) :
    H.toHistory.IsPrefixOf (H.attach T hT S hS).toHistory := by
  let E := (H.attach T hT S hS).toHistory
  refine ⟨hT, ?_⟩
  let b : Icc (0 : ℝ) E.horizon := ⟨H.horizon, H.horizon_nonneg, hT⟩
  have hb : b.1 = H.horizon := rfl
  have ha : E.activeStage b = Fin.last H.eventCount := by
    refine E.activeStage_eq_of_maximal b (Fin.last H.eventCount) ?_ (fun _ _ => Fin.le_last _)
    rw [hb]
    exact H.time_le_horizon
  have hc : (E.restrict b).eventCount = H.eventCount := congrArg Fin.val ha
  refine {
    horizon_eq := ?_
    count_eq := hc
    time_eq := fun _ => rfl
    stage_eq := fun _ => rfl
    initialMetric_heq := fun _ => HEq.rfl
    event_eq := fun _ => MetricCutCapEvent.SamePresentation.refl _
    metric_heq := ?_ }
  · rw [ObservedHistory.restrict_horizon, hb]
  intro j t ht
  refine (E.restrict_stageMetric b j t ht).trans ?_
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · change HEq
      (E.stageMetric ((Fin.castLE (Nat.le_of_lt_succ (E.activeStage b).isLt) i).castSucc) t)
      (H.toHistory.stageMetric ((Fin.cast hc i).castSucc) t)
    exact (heq_of_eq (ObservedHistory.stageMetric_castSucc_apply (H := E)
        (Fin.castLE (Nat.le_of_lt_succ (E.activeStage b).isLt) i) t)).trans
      (heq_of_eq (ObservedHistory.stageMetric_castSucc_apply (H := H.toHistory)
        (Fin.cast hc i) t)).symm
  · have hidxE : Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (E.activeStage b).isLt) 1)
        (Fin.last (E.restrict b).eventCount) =
        (Fin.last H.eventCount : Fin (E.eventCount + 1)) := by
      refine Fin.ext ?_
      have h1 : (Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (E.activeStage b).isLt) 1)
          (Fin.last (E.restrict b).eventCount)).val = (E.restrict b).eventCount := rfl
      have h2 : ((Fin.last H.eventCount : Fin (E.eventCount + 1))).val = H.eventCount := rfl
      rw [h1, h2, hc]
    have hidxH : Fin.cast (congrArg (· + 1) hc) (Fin.last (E.restrict b).eventCount)
        = Fin.last H.eventCount := by
      refine Fin.ext ?_
      have h1 : (Fin.cast (congrArg (· + 1) hc)
          (Fin.last (E.restrict b).eventCount)).val = (E.restrict b).eventCount := rfl
      have h2 : (Fin.last H.eventCount).val = H.eventCount := rfl
      rw [h1, h2, hc]
    rw [hidxE, hidxH]
    have hrestrict_time : (E.restrict b).time (Fin.last (E.restrict b).eventCount) =
        H.toHistory.horizon := by
      rw [ObservedHistory.restrict_time_last E b ha]
      show E.time (Fin.last E.eventCount) = H.toHistory.horizon
      rw [show E.time (Fin.last E.eventCount) = H.time (Fin.last H.eventCount) from rfl, htime]
    have ht_eq : t = H.toHistory.horizon := by
      have h1 := ht
      rw [ObservedHistory.mem_stageDomain_last] at h1
      rw [ObservedHistory.restrict_horizon, hb, hrestrict_time] at h1
      exact le_antisymm h1.2 h1.1
    subst ht_eq
    have hR : H.toHistory.stageMetric (Fin.last H.eventCount) H.toHistory.horizon =
        H.toHistory.initialMetric (Fin.last H.eventCount) :=
      ObservedHistory.stageMetric_last_of_le (H := H.toHistory) (le_of_eq htime.symm) _
    rw [hR]
    by_cases hlt : H.time (Fin.last H.eventCount) < T
    · have hL : E.stageMetric (Fin.last H.eventCount) H.toHistory.horizon =
          (E.finalSlab hlt).flow.base.metric H.toHistory.horizon :=
        ObservedHistory.stageMetric_last_of_lt (H := E) (h := hlt) _
      rw [hL]
      have hmid : (E.finalSlab hlt).flow.base.metric H.toHistory.horizon =
          (S hlt).flow.base.metric (H.time (Fin.last H.eventCount)) := by
        rw [show H.toHistory.horizon = H.time (Fin.last H.eventCount) from htime.symm]
        rfl
      exact heq_of_eq (hmid.trans (hS hlt))
    · have hTeq : T = H.horizon := le_antisymm (not_lt.mp (htime ▸ hlt)) hT
      have hnot : ¬ E.time (Fin.last E.eventCount) < E.horizon := by
        rw [show E.time (Fin.last E.eventCount) = H.time (Fin.last H.eventCount) from rfl,
          htime, show E.horizon = T from rfl, hTeq]
        exact lt_irrefl _
      have hL : E.stageMetric (Fin.last H.eventCount) H.toHistory.horizon =
          E.initialMetric (Fin.last E.eventCount) :=
        ObservedHistory.stageMetric_last_of_le (H := E) (not_lt.mp hnot) _
      rw [hL]
      exact HEq.rfl

end RetainedCoreHistory

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

private structure Layer (C : RetainedCoreTimedEventChain P g) (m : ℕ)
    (Hprev : RetainedCoreHistory.{u}) where
  history : RetainedCoreHistory.{u}
  eventCount_eq : history.eventCount = m + 1
  horizon_eq : history.horizon = (m : ℝ) + 1
  time_last_eq : history.time (Fin.last history.eventCount) = C.time (m + 1)
  stage_last_eq : history.stage (Fin.last history.eventCount) = C.stage (m + 1)
  metric_last_heq : HEq (history.initialMetric (Fin.last history.eventCount)) (C.metric (m + 1))
  cap_metric_heq : ∀ (h : history.time (Fin.last history.eventCount) <
      history.horizon) (τ : ℝ),
    HEq ((history.finalSlab h).flow.base.metric τ)
      ((C.event (m + 1)).toMetricCutCapEvent.incoming.flow.base.metric τ)
  restrict_prev : ((history.toHistory).restrict
      ⟨(m : ℝ), Nat.cast_nonneg m, by
        change (m : ℝ) ≤ history.horizon
        linarith [horizon_eq]⟩).SamePresentation Hprev.toHistory
  initial : InitialIdentification P g history.toHistory
  initial_heq : HEq initial.map (InitialIdentification.atZero P g).map

private def layerCore (C : RetainedCoreTimedEventChain P g) (m : ℕ) {H : RetainedCoreHistory.{u}}
    (A : InitialIdentification P g H.toHistory)
    (heventCount : H.eventCount = m) (hhorizon : H.horizon = (m : ℝ))
    (hstage : H.stage (Fin.last H.eventCount) = C.stage m)
    (htime : H.time (Fin.last H.eventCount) = C.time m)
    (hmetric : HEq (H.initialMetric (Fin.last H.eventCount)) (C.metric m))
    (hA : HEq A.map (InitialIdentification.atZero P g).map)
    (hcompat : H.appendEventCompatible
      (RetainedCoreEvent.transport hstage.symm rfl htime.symm rfl (C.event m))) :
    Layer C m H := by
  have hs : H.time (Fin.last H.eventCount) < C.time (m + 1) := by
    rw [htime]
    exact C.time_lt_succ m
  let E := RetainedCoreEvent.transport hstage.symm rfl htime.symm rfl (C.event m)
  have hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount) :=
    eq_of_heq ((RetainedCoreEvent.transport_incoming_metric_heq hstage.symm rfl htime.symm rfl
      (C.event m) (H.time (Fin.last H.eventCount))).trans
      ((heq_of_eq (congrArg (fun t : ℝ =>
        (C.event m).toMetricCutCapEvent.incoming.flow.base.metric t) htime)).trans
        ((heq_of_eq (C.event_initial m)).trans hmetric.symm)))
  let H₁ := H.appendEvent hs E hinit
  have hstage₁ : H₁.stage (Fin.last H₁.eventCount) = C.stage (m + 1) :=
    RetainedCoreHistory.appendEvent_stage_last H hs E hinit
  have htime₁ : H₁.time (Fin.last H₁.eventCount) = C.time (m + 1) :=
    RetainedCoreHistory.appendEvent_time_last H hs E hinit
  have hcount₁ : H₁.eventCount = m + 1 := by
    rw [RetainedCoreHistory.appendEvent_eventCount, heventCount]
  have hmetric₁ : HEq (H₁.initialMetric (Fin.last H₁.eventCount)) (C.metric (m + 1)) :=
    (RetainedCoreHistory.appendEvent_initialMetric_last_heq H hs E hinit).trans
      ((RetainedCoreEvent.transport_outputMetric_heq hstage.symm rfl htime.symm rfl
        (C.event m)).trans (heq_of_eq (C.event_output m)))
  have hle : H₁.horizon ≤ (m : ℝ) + 1 := by
    rw [RetainedCoreHistory.appendEvent_horizon]
    exact C.time_le m
  have hpure : H₁.time (Fin.last H₁.eventCount) = H₁.horizon :=
    htime₁.trans (RetainedCoreHistory.appendEvent_horizon H hs E hinit).symm
  have hgt : (m : ℝ) + 1 < C.time (m + 2) := by
    have h := C.time_gt (m + 1)
    push_cast at h
    exact h
  let E' := RetainedCoreEvent.transport hstage₁.symm rfl htime₁.symm rfl (C.event (m + 1))
  let S : (h : H₁.time (Fin.last H₁.eventCount) < (m : ℝ) + 1) →
      (H₁.stage (Fin.last H₁.eventCount)).ClosedSlab (H₁.time (Fin.last H₁.eventCount))
        ((m : ℝ) + 1) :=
    fun h => (E'.toMetricCutCapEvent.incoming).closedPrefix ((m : ℝ) + 1) h hgt
  have hS : ∀ h, (S h).flow.base.metric (H₁.time (Fin.last H₁.eventCount)) =
      H₁.initialMetric (Fin.last H₁.eventCount) := by
    intro h
    refine eq_of_heq ((heq_of_eq (closedPrefix_flow_metric _ h hgt _)).trans ?_)
    exact (RetainedCoreEvent.transport_incoming_metric_heq hstage₁.symm rfl htime₁.symm rfl
      (C.event (m + 1)) (H₁.time (Fin.last H₁.eventCount))).trans
      ((heq_of_eq (congrArg (fun t : ℝ =>
        (C.event (m + 1)).toMetricCutCapEvent.incoming.flow.base.metric t) htime₁)).trans
        ((heq_of_eq (C.event_initial (m + 1))).trans hmetric₁.symm))
  have hpref : H.toHistory.IsPrefixOf (H₁.attach ((m : ℝ) + 1) hle S hS).toHistory :=
    (RetainedCoreHistory.appendEvent_isPrefixOf H hs E hinit
        (by rw [hhorizon]; exact C.time_gt m) hcompat).trans
      (RetainedCoreHistory.attach_isPrefixOf H₁ ((m : ℝ) + 1) hle S hS hpure)
  have hAttachEventCount : (H₁.attach ((m : ℝ) + 1) hle S hS).eventCount =
      H₁.eventCount := rfl
  have hAttachHorizon : (H₁.attach ((m : ℝ) + 1) hle S hS).horizon = (m : ℝ) + 1 := rfl
  have hAttachTime : (H₁.attach ((m : ℝ) + 1) hle S hS).time
      (Fin.last (H₁.attach ((m : ℝ) + 1) hle S hS).eventCount) =
      H₁.time (Fin.last H₁.eventCount) := rfl
  have hAttachStage : (H₁.attach ((m : ℝ) + 1) hle S hS).stage
      (Fin.last (H₁.attach ((m : ℝ) + 1) hle S hS).eventCount) =
      H₁.stage (Fin.last H₁.eventCount) := rfl
  have hAttachInitial : HEq ((H₁.attach ((m : ℝ) + 1) hle S hS).initialMetric
      (Fin.last (H₁.attach ((m : ℝ) + 1) hle S hS).eventCount))
      (H₁.initialMetric (Fin.last H₁.eventCount)) := HEq.rfl
  have hAttachZero : (H₁.attach ((m : ℝ) + 1) hle S hS).stage 0 = H₁.stage 0 := rfl
  have hAttachZeroMetric : HEq ((H₁.attach ((m : ℝ) + 1) hle S hS).initialMetric 0)
      (H₁.initialMetric 0) := HEq.rfl
  have hstageZero : (H₁.attach ((m : ℝ) + 1) hle S hS).toHistory.stage 0 =
      H.toHistory.stage 0 :=
    hAttachZero.trans (RetainedCoreHistory.appendEvent_stage_castSucc H hs E hinit 0)
  have hmetricZero : HEq ((H₁.attach ((m : ℝ) + 1) hle S hS).toHistory.initialMetric 0)
      (H.toHistory.initialMetric 0) :=
    hAttachZeroMetric.trans
      (RetainedCoreHistory.appendEvent_initialMetric_castSucc_heq H hs E hinit 0)
  have hAttachSlab (h : (H₁.attach ((m : ℝ) + 1) hle S hS).time
      (Fin.last (H₁.attach ((m : ℝ) + 1) hle S hS).eventCount) <
      (H₁.attach ((m : ℝ) + 1) hle S hS).horizon) (τ : ℝ) :
      HEq (((H₁.attach ((m : ℝ) + 1) hle S hS).finalSlab h).flow.base.metric τ)
        ((S h).flow.base.metric τ) := HEq.rfl
  refine {
    history := H₁.attach ((m : ℝ) + 1) hle S hS
    eventCount_eq := hAttachEventCount.trans hcount₁
    horizon_eq := hAttachHorizon
    time_last_eq := hAttachTime.trans htime₁
    stage_last_eq := hAttachStage.trans hstage₁
    metric_last_heq := hAttachInitial.trans hmetric₁
    cap_metric_heq := ?_
    restrict_prev := ?_
    initial := InitialIdentification.ofStageZero A hstageZero hmetricZero
    initial_heq := (InitialIdentification.map_of_stageZero_heq A hstageZero hmetricZero).trans hA }
  · intro h τ
    exact (hAttachSlab h τ).trans ((heq_of_eq (closedPrefix_flow_metric _ h hgt τ)).trans
      (RetainedCoreEvent.transport_incoming_metric_heq hstage₁.symm rfl htime₁.symm rfl
        (C.event (m + 1)) τ))
  · have hpres := hpref.presentation
    have hpt : (⟨(H.toHistory).horizon, (H.toHistory).horizon_nonneg, hpref.horizon_le⟩ :
        Icc (0 : ℝ) (H₁.attach ((m : ℝ) + 1) hle S hS).horizon) =
        ⟨(m : ℝ), Nat.cast_nonneg m,
          by change (m : ℝ) ≤ (H₁.attach ((m : ℝ) + 1) hle S hS).horizon
             linarith [hAttachHorizon]⟩ := Subtype.ext hhorizon
    rw [hpt] at hpres
    exact hpres

private def layerZero (C : RetainedCoreTimedEventChain P g) :
    Layer C 0 (RetainedCoreHistory.atZero P g) :=
  layerCore C 0 (InitialIdentification.atZero P g) rfl (by norm_num) C.stage_zero.symm
    C.time_zero.symm C.metric_zero.symm HEq.rfl
    (RetainedCoreHistory.appendEventCompatible_of_time_eq_horizon _ _ rfl)

private def layerStep (C : RetainedCoreTimedEventChain P g) (m : ℕ)
    {Hprev : RetainedCoreHistory.{u}} (L : Layer C m Hprev) : Layer C (m + 1) L.history :=
  layerCore C (m + 1) L.initial L.eventCount_eq
    (by rw [L.horizon_eq]; push_cast; ring) L.stage_last_eq L.time_last_eq
    L.metric_last_heq L.initial_heq
    (by
      intro h τ _
      exact eq_of_heq ((RetainedCoreEvent.transport_incoming_metric_heq L.stage_last_eq.symm rfl
        L.time_last_eq.symm rfl (C.event (m + 1)) τ).trans (L.cap_metric_heq h τ).symm))

private def layerSigma (C : RetainedCoreTimedEventChain P g) :
    (m : ℕ) → Sigma fun H : RetainedCoreHistory.{u} => Layer C m H
  | 0 => ⟨RetainedCoreHistory.atZero P g, layerZero C⟩
  | m + 1 => ⟨(layerSigma C m).2.history, layerStep C m (layerSigma C m).2⟩

private theorem ObservedHistory.restrict_congr {H : ObservedHistory.{u}}
    {b b' : Icc (0 : ℝ) H.horizon} (h : b = b') :
    (H.restrict b).SamePresentation (H.restrict b') := by
  subst h
  exact ObservedHistory.SamePresentation.refl _

namespace RetainedCoreTimedEventChain

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

def toRetainedCoreTimedObservationTower (C : RetainedCoreTimedEventChain P g) :
    RetainedCoreObservationTower P g where
  history n := Nat.casesOn n (RetainedCoreHistory.atZero P g) (fun m => (layerSigma C m).2.history)
  horizon_eq n := by
    cases n with
    | zero => exact Nat.cast_zero.symm
    | succ m =>
      rw [show (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 by push_cast; ring]
      exact (layerSigma C m).2.horizon_eq
  initial n := by
    cases n with
    | zero => exact InitialIdentification.atZero P g
    | succ m => exact (layerSigma C m).2.initial
  successor n := by
    cases n with
    | zero =>
      refine (ObservedHistory.restrict_congr (Subtype.ext rfl)).trans
        (layerSigma C 0).2.restrict_prev
    | succ m =>
      refine (ObservedHistory.restrict_congr (Subtype.ext rfl)).trans
        (layerSigma C (m + 1)).2.restrict_prev
  initial_successor n := by
    cases n with
    | zero =>
      exact (heq_of_eq (InitialIdentification.restrict_map _ _)).trans
        (layerSigma C 0).2.initial_heq
    | succ m =>
      exact (heq_of_eq (InitialIdentification.restrict_map _ _)).trans
        (((layerSigma C (m + 1)).2.initial_heq).trans ((layerSigma C m).2.initial_heq).symm)

theorem toRetainedCoreTimedObservationTower_history_eventCount (C : RetainedCoreTimedEventChain P g)
    (n : ℕ) : (C.toRetainedCoreTimedObservationTower.history n).eventCount = n := by
  cases n with
  | zero => rfl
  | succ m => exact (layerSigma C m).2.eventCount_eq

theorem toRetainedCoreTimedObservationTower_history_stage_last (C : RetainedCoreTimedEventChain P g)
    (n : ℕ) :
    (C.toRetainedCoreTimedObservationTower.history n).stage
        (Fin.last (C.toRetainedCoreTimedObservationTower.history n).eventCount) = C.stage n := by
  cases n with
  | zero => exact C.stage_zero.symm
  | succ m => exact (layerSigma C m).2.stage_last_eq

theorem toRetainedCoreTimedObservationTower_history_time_last (C : RetainedCoreTimedEventChain P g)
    (n : ℕ) :
    (C.toRetainedCoreTimedObservationTower.history n).time
        (Fin.last (C.toRetainedCoreTimedObservationTower.history n).eventCount) = C.time n := by
  cases n with
  | zero => exact C.time_zero.symm
  | succ m => exact (layerSigma C m).2.time_last_eq

end RetainedCoreTimedEventChain

theorem hasSurgeryContinuationTower_of_retainedCoreTimedEventChain
    {P : OrientedThreeStage.{u}} {g : P.Metric} (C : RetainedCoreTimedEventChain P g)
    (hrecords : C.toRetainedCoreTimedObservationTower.HasUniformCutoffRecords)
    (hbfr : C.toRetainedCoreTimedObservationTower.hasBoundaryFrameReversing)
    (hctrl : C.toRetainedCoreTimedObservationTower.hasPoincareStandardDiscarded) :
    HasSurgeryContinuationTower P g :=
  hasSurgeryContinuationTower_of_uniformCutoffRecords C.toRetainedCoreTimedObservationTower
    hrecords hbfr hctrl

namespace RetainedCoreEventChain

def toRetainedCoreTimedEventChain {P : OrientedThreeStage.{u}} {g : P.Metric}
    (C : RetainedCoreEventChain P g) : RetainedCoreTimedEventChain P g where
  time n := (n : ℝ)
  time_zero := Nat.cast_zero
  time_gt n := by
    push_cast
    linarith
  time_le n := by
    push_cast
    linarith
  stage := C.stage
  metric := C.metric
  stage_zero := C.stage_zero
  metric_zero := C.metric_zero
  event n := RetainedCoreEvent.transport rfl rfl rfl (by push_cast; ring) (C.event n)
  event_initial n :=
    eq_of_heq ((RetainedCoreEvent.transport_incoming_metric_heq rfl rfl rfl (by push_cast; ring)
      (C.event n) (n : ℝ)).trans (heq_of_eq (C.event_initial n)))
  event_output n :=
    eq_of_heq ((RetainedCoreEvent.transport_outputMetric_heq rfl rfl rfl (by push_cast; ring)
      (C.event n)).trans (heq_of_eq (C.event_output n)))

end RetainedCoreEventChain

theorem exists_surgeryTime_zero_gt_le_strict :
    ∃ time : ℕ → ℝ, time 0 = 0 ∧ (∀ n : ℕ, (n : ℝ) < time (n + 1)) ∧
      (∀ n : ℕ, time (n + 1) ≤ (n : ℝ) + 1) ∧
      (∀ n : ℕ, time (n + 1) < (n : ℝ) + 1) := by
  refine ⟨fun n => if n = 0 then 0 else (n : ℝ) - 1 / 2, rfl, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    rw [ite_eq_right (Nat.succ_ne_zero n)]
    push_cast
    linarith
  · intro n
    dsimp only
    rw [ite_eq_right (Nat.succ_ne_zero n)]
    push_cast
    norm_num
  · intro n
    dsimp only
    rw [ite_eq_right (Nat.succ_ne_zero n)]
    push_cast
    linarith

theorem exists_surgeryTime_zero_eq :
    ∃ time : ℕ → ℝ, time 0 = 0 ∧ (∀ n : ℕ, (n : ℝ) < time (n + 1)) ∧
      (∀ n : ℕ, time (n + 1) ≤ (n : ℝ) + 1) ∧
      (∀ n : ℕ, time (n + 1) = ((n + 1 : ℕ) : ℝ)) := by
  refine ⟨fun n => (n : ℝ), Nat.cast_zero, ?_, ?_, ?_⟩
  · intro n
    push_cast
    linarith
  · intro n
    push_cast
    linarith
  · intro n
    push_cast
    ring

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
