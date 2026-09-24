import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalClassRealizationLocality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurgeryContinuationTowerProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private structure StageIdentification (P : OrientedThreeStage.{u}) (g : P.Metric)
    (X : OrientedThreeStage.{u}) (m : X.Metric) where
  map : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ X.Carrier
  positive : PreservesTangentOrientation P.orientation X.orientation map
  metric_eq : ∀ x : P.Carrier, ∀ v w : TangentSpace ThreeModel x,
    m.inner (map x) (mfderiv ThreeModel ThreeModel map x v)
        (mfderiv ThreeModel ThreeModel map x w) = g.inner x v w

namespace StageIdentification

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

private def ofInitial {K : ObservedHistory.{u}} (A : InitialIdentification P g K) :
    StageIdentification P g (K.stage 0) (K.initialMetric 0) where
  map := A.map
  positive := A.positive
  metric_eq := A.metric_eq

private def toInitial {K : ObservedHistory.{u}}
    (B : StageIdentification P g (K.stage 0) (K.initialMetric 0)) :
    InitialIdentification P g K where
  map := B.map
  positive := B.positive
  metric_eq := B.metric_eq

private def cast {X X' : OrientedThreeStage.{u}} {m : X.Metric} {m' : X'.Metric}
    (A : StageIdentification P g X m) (hX : X' = X) (hm : HEq m' m) :
    StageIdentification P g X' m' :=
  let hp : (⟨X', m'⟩ : Sigma fun Y : OrientedThreeStage.{u} => Y.Metric) = ⟨X, m⟩ := by
    cases hX
    exact Sigma.ext rfl hm
  Eq.ndrec (motive := fun p : Sigma fun Y : OrientedThreeStage.{u} => Y.Metric =>
    StageIdentification P g p.1 p.2) A hp.symm

private theorem cast_map_heq {X X' : OrientedThreeStage.{u}} {m : X.Metric} {m' : X'.Metric}
    (A : StageIdentification P g X m) (hX : X' = X) (hm : HEq m' m) :
    HEq (cast A hX hm).map A.map := by
  cases hX
  cases hm
  exact HEq.rfl

end StageIdentification

def InitialIdentification.of_stageZero {P : OrientedThreeStage.{u}} {g : P.Metric}
    {H K : ObservedHistory.{u}} (A : InitialIdentification P g H)
    (hstage : K.stage 0 = H.stage 0) (hmetric : HEq (K.initialMetric 0) (H.initialMetric 0)) :
    InitialIdentification P g K :=
  (StageIdentification.cast (StageIdentification.ofInitial A) hstage hmetric).toInitial

theorem InitialIdentification.map_of_stageZero_heq {P : OrientedThreeStage.{u}} {g : P.Metric}
    {H K : ObservedHistory.{u}} (A : InitialIdentification P g H)
    (hstage : K.stage 0 = H.stage 0) (hmetric : HEq (K.initialMetric 0) (H.initialMetric 0)) :
    HEq (InitialIdentification.of_stageZero A hstage hmetric).map A.map :=
  StageIdentification.cast_map_heq (StageIdentification.ofInitial A) hstage hmetric

def InitialIdentification.atZero (P : OrientedThreeStage.{u}) (g : P.Metric) :
    InitialIdentification P g (RetainedCoreHistory.atZero P g).toHistory where
  map := Diffeomorph.refl ThreeModel P.Carrier ∞
  positive := preservesTangentOrientation_refl P.orientation
  metric_eq := by
    intro x v w
    simp only [Diffeomorph.coe_refl, mfderiv_id]
    rfl

namespace ObservedHistory

private theorem stageMetric_last_of_lt' (H : ObservedHistory.{u})
    (h : H.time (Fin.last H.eventCount) < H.horizon) (τ : ℝ) :
    H.stageMetric (Fin.last H.eventCount) τ = (H.finalSlab h).flow.base.metric τ := by
  rw [ObservedHistory.stageMetric, Fin.lastCases_last, dif_pos h]

private theorem stageMetric_last_of_le' (H : ObservedHistory.{u})
    (h : H.horizon ≤ H.time (Fin.last H.eventCount)) (τ : ℝ) :
    H.stageMetric (Fin.last H.eventCount) τ = H.initialMetric (Fin.last H.eventCount) := by
  rw [ObservedHistory.stageMetric, Fin.lastCases_last, dif_neg (not_lt.mpr h)]

private theorem mem_stageDomain_last' (H : ObservedHistory.{u}) (τ : ℝ) :
    τ ∈ H.stageDomain (Fin.last H.eventCount) ↔
      τ ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon := by
  rw [ObservedHistory.stageDomain, Fin.lastCases_last]

private theorem restrict_time_last' (K : ObservedHistory.{u}) (b : Icc (0 : ℝ) K.horizon)
    (hb : K.activeStage b = Fin.last K.eventCount) :
    (K.restrict b).time (Fin.last (K.restrict b).eventCount) = K.time (Fin.last K.eventCount) := by
  have h := ObservedHistory.restrict_time_apply K b (Fin.last ((K.activeStage b).val))
  exact h.trans (congrArg K.time (Fin.ext (by simp [hb])))

end ObservedHistory

namespace RetainedCoreHistory

variable {P : OrientedThreeStage.{u}}

private theorem appendEvent_toHistory_stage_zero (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.appendEvent hs E hinit).toHistory.stage 0 = H.toHistory.stage 0 :=
  appendEvent_stage_castSucc H hs E hinit 0

private theorem appendEvent_toHistory_initialMetric_zero_heq (H : RetainedCoreHistory P)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    HEq ((H.appendEvent hs E hinit).toHistory.initialMetric 0) (H.toHistory.initialMetric 0) :=
  appendEvent_initialMetric_castSucc_heq H hs E hinit 0

private theorem extendHorizon_restrict_samePresentation_of_time_eq_horizon
    (H : RetainedCoreHistory P) (T : ℝ) (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    (b : Icc (0 : ℝ) (H.extendHorizon T hT S hS).toHistory.horizon) (hb : b.1 = H.horizon) :
    (((H.extendHorizon T hT S hS).toHistory).restrict b).SamePresentation H.toHistory := by
  let E := (H.extendHorizon T hT S hS).toHistory
  have ha : E.activeStage b = Fin.last H.eventCount := by
    refine E.activeStage_eq_of_maximal b _ ?_ (fun _ _ => Fin.le_last _)
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
      rw [ObservedHistory.restrict_time_last' E b ha]
      show E.time (Fin.last E.eventCount) = H.toHistory.horizon
      rw [show E.time (Fin.last E.eventCount) = H.time (Fin.last H.eventCount) from rfl, htime]
    have ht_eq : t = H.toHistory.horizon := by
      have h1 := ht
      rw [ObservedHistory.mem_stageDomain_last'] at h1
      rw [ObservedHistory.restrict_horizon, hb, hrestrict_time] at h1
      exact le_antisymm h1.2 h1.1
    subst ht_eq
    by_cases hlt : H.toHistory.horizon < T
    · have hcond : E.time (Fin.last E.eventCount) < E.horizon := by
        rw [show E.time (Fin.last E.eventCount) = H.time (Fin.last H.eventCount) from rfl, htime,
          show E.horizon = T from rfl]
        exact hlt
      have hL : E.stageMetric (Fin.last H.eventCount) (H.toHistory.horizon) =
          (E.finalSlab hcond).flow.base.metric (H.toHistory.horizon) :=
        ObservedHistory.stageMetric_last_of_lt' E hcond (H.toHistory.horizon)
      have hR : H.toHistory.stageMetric (Fin.last H.eventCount) (H.toHistory.horizon) =
          H.toHistory.initialMetric (Fin.last H.eventCount) :=
        ObservedHistory.stageMetric_last_of_le' H.toHistory (le_of_eq htime.symm)
          (H.toHistory.horizon)
      rw [hL, hR]
      have hmid : (E.finalSlab hcond).flow.base.metric H.toHistory.horizon =
          S.flow.base.metric (H.time (Fin.last H.eventCount)) := by
        rw [show H.toHistory.horizon = H.time (Fin.last H.eventCount) from htime.symm]
        rfl
      exact heq_of_eq (hmid.trans hS)
    · have hTeq : T = H.toHistory.horizon := le_antisymm (not_lt.mp hlt) hT
      have hcond : ¬ E.time (Fin.last E.eventCount) < E.horizon := by
        rw [show E.time (Fin.last E.eventCount) = H.time (Fin.last H.eventCount) from rfl, htime,
          show E.horizon = T from rfl, hTeq]
        exact lt_irrefl _
      have hL : E.stageMetric (Fin.last H.eventCount) (H.toHistory.horizon) =
          E.initialMetric (Fin.last H.eventCount) :=
        ObservedHistory.stageMetric_last_of_le' E (not_lt.mp hcond) (H.toHistory.horizon)
      have hR : H.toHistory.stageMetric (Fin.last H.eventCount) (H.toHistory.horizon) =
          H.toHistory.initialMetric (Fin.last H.eventCount) :=
        ObservedHistory.stageMetric_last_of_le' H.toHistory (le_of_eq htime.symm)
          (H.toHistory.horizon)
      rw [hL, hR]
      rfl

theorem extendHorizon_isPrefixOf_of_time_eq_horizon (H : RetainedCoreHistory P) (T : ℝ)
    (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (htime : H.time (Fin.last H.eventCount) = H.horizon) :
    H.toHistory.IsPrefixOf (H.extendHorizon T hT S hS).toHistory :=
  ⟨hT.trans (le_of_eq (show (H.extendHorizon T hT S hS).toHistory.horizon = T from rfl).symm),
    extendHorizon_restrict_samePresentation_of_time_eq_horizon H T hT S hS htime
      ⟨H.horizon, H.horizon_nonneg,
        hT.trans (le_of_eq
          (show (H.extendHorizon T hT S hS).toHistory.horizon = T from rfl).symm)⟩ rfl⟩

end RetainedCoreHistory

structure RetainedCoreEventChain (P : OrientedThreeStage.{u}) (g : P.Metric) where
  stage : ℕ → OrientedThreeStage.{u}
  metric : (n : ℕ) → (stage n).Metric
  stage_zero : stage 0 = P
  metric_zero : HEq (metric 0) g
  event : (n : ℕ) → RetainedCoreEvent (stage n) (stage (n + 1)) (n : ℝ) ((n : ℝ) + 1)
  event_initial : ∀ n : ℕ,
    (event n).toMetricCutCapEvent.incoming.flow.base.metric (n : ℝ) = metric n
  event_output : ∀ n : ℕ, (event n).toMetricCutCapEvent.outputMetric = metric (n + 1)

namespace RetainedCoreEventChain

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

private structure AlignedLayer (C : RetainedCoreEventChain P g) (n : ℕ) where
  history : RetainedCoreHistory P
  eventCount_eq : history.eventCount = n
  horizon_eq : history.horizon = (n : ℝ)
  time_last_eq : history.time (Fin.last history.eventCount) = (n : ℝ)
  stage_last_eq : history.stage (Fin.last history.eventCount) = C.stage n
  metric_last_heq : HEq (history.initialMetric (Fin.last history.eventCount)) (C.metric n)
  initial : InitialIdentification P g history.toHistory

private theorem nextTimeLt (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    L.history.time (Fin.last L.history.eventCount) < ((n : ℝ) + 1) := by
  rw [L.time_last_eq]
  exact lt_add_one _

private def nextEvent (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    RetainedCoreEvent (L.history.stage (Fin.last L.history.eventCount)) (C.stage (n + 1))
      (L.history.time (Fin.last L.history.eventCount)) ((n : ℝ) + 1) :=
  RetainedCoreEvent.transport L.stage_last_eq.symm rfl L.time_last_eq.symm rfl (C.event n)

private theorem nextEvent_incoming_heq (C : RetainedCoreEventChain P g) (n : ℕ)
    (L : AlignedLayer C n) :
    HEq ((C.nextEvent n L).toMetricCutCapEvent.incoming.flow.base.metric
        (L.history.time (Fin.last L.history.eventCount)))
      (C.metric n) :=
  (RetainedCoreEvent.transport_incoming_metric_heq L.stage_last_eq.symm rfl
    L.time_last_eq.symm rfl (C.event n)
    (L.history.time (Fin.last L.history.eventCount))).trans
    ((heq_of_eq (congrArg
      (fun t : ℝ => (C.event n).toMetricCutCapEvent.incoming.flow.base.metric t)
      L.time_last_eq)).trans (heq_of_eq (C.event_initial n)))

private theorem nextInit (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextEvent n L).toMetricCutCapEvent.incoming.flow.base.metric
        (L.history.time (Fin.last L.history.eventCount)) =
      L.history.initialMetric (Fin.last L.history.eventCount) :=
  eq_of_heq ((C.nextEvent_incoming_heq n L).trans L.metric_last_heq.symm)

private def nextHistory (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    RetainedCoreHistory P :=
  L.history.appendEvent (C.nextTimeLt n L) (C.nextEvent n L) (C.nextInit n L)

private theorem nextEventCountEq (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextHistory n L).eventCount = n + 1 := by
  rw [nextHistory, RetainedCoreHistory.appendEvent_eventCount, L.eventCount_eq]

private theorem nextStageZero (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextHistory n L).toHistory.stage 0 = L.history.toHistory.stage 0 :=
  RetainedCoreHistory.appendEvent_toHistory_stage_zero L.history (C.nextTimeLt n L)
    (C.nextEvent n L) (C.nextInit n L)

private theorem nextInitialMetricHeq (C : RetainedCoreEventChain P g) (n : ℕ)
    (L : AlignedLayer C n) :
    HEq ((C.nextHistory n L).toHistory.initialMetric 0) (L.history.toHistory.initialMetric 0) :=
  RetainedCoreHistory.appendEvent_toHistory_initialMetric_zero_heq L.history (C.nextTimeLt n L)
    (C.nextEvent n L) (C.nextInit n L)

private theorem nextHorizonEq (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextHistory n L).horizon = ((n + 1 : ℕ) : ℝ) := by
  rw [nextHistory, RetainedCoreHistory.appendEvent_horizon]
  push_cast
  ring

private theorem nextTimeLastEq (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextHistory n L).time (Fin.last (C.nextHistory n L).eventCount) = ((n + 1 : ℕ) : ℝ) := by
  rw [nextHistory]
  change (L.history.appendEvent (C.nextTimeLt n L) (C.nextEvent n L) (C.nextInit n L)).time
    (Fin.last (L.history.eventCount + 1)) = ((n + 1 : ℕ) : ℝ)
  rw [RetainedCoreHistory.appendEvent_time_last]
  push_cast
  ring

private theorem nextStageLastEq (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    (C.nextHistory n L).stage (Fin.last (C.nextHistory n L).eventCount) = C.stage (n + 1) :=
  RetainedCoreHistory.appendEvent_stage_last L.history (C.nextTimeLt n L) (C.nextEvent n L)
    (C.nextInit n L)

private theorem nextMetricLastHeq (C : RetainedCoreEventChain P g) (n : ℕ)
    (L : AlignedLayer C n) :
    HEq ((C.nextHistory n L).initialMetric (Fin.last (C.nextHistory n L).eventCount))
      (C.metric (n + 1)) :=
  (RetainedCoreHistory.appendEvent_initialMetric_last_heq L.history (C.nextTimeLt n L)
      (C.nextEvent n L) (C.nextInit n L)).trans
    ((RetainedCoreEvent.transport_outputMetric_heq L.stage_last_eq.symm rfl L.time_last_eq.symm rfl
      (C.event n)).trans (heq_of_eq (C.event_output n)))

private def alignedLayerZero (C : RetainedCoreEventChain P g) : AlignedLayer C 0 where
  history := RetainedCoreHistory.atZero P g
  eventCount_eq := rfl
  horizon_eq := by simp
  time_last_eq := by simp
  stage_last_eq := C.stage_zero.symm
  metric_last_heq := C.metric_zero.symm
  initial := InitialIdentification.atZero P g

private def alignedLayerStep (C : RetainedCoreEventChain P g) (n : ℕ) (L : AlignedLayer C n) :
    AlignedLayer C (n + 1) where
  history := C.nextHistory n L
  eventCount_eq := C.nextEventCountEq n L
  horizon_eq := C.nextHorizonEq n L
  time_last_eq := C.nextTimeLastEq n L
  stage_last_eq := C.nextStageLastEq n L
  metric_last_heq := C.nextMetricLastHeq n L
  initial := InitialIdentification.of_stageZero L.initial (C.nextStageZero n L)
    (C.nextInitialMetricHeq n L)

private def alignedLayer (C : RetainedCoreEventChain P g) (n : ℕ) : AlignedLayer C n :=
  Nat.rec (alignedLayerZero C) (fun n L => alignedLayerStep C n L) n

private theorem alignedLayer_succ (C : RetainedCoreEventChain P g) (n : ℕ) :
    C.alignedLayer (n + 1) = C.alignedLayerStep n (C.alignedLayer n) := rfl

private theorem alignedLayer_prefix (C : RetainedCoreEventChain P g) (n : ℕ) :
    (C.alignedLayer n).history.toHistory.IsPrefixOf
      (C.alignedLayer (n + 1)).history.toHistory := by
  rw [alignedLayer_succ]
  refine RetainedCoreHistory.appendEvent_isPrefixOf (C.alignedLayer n).history (C.nextTimeLt n _)
    (C.nextEvent n _) (C.nextInit n _) ?_ ?_
  · rw [(C.alignedLayer n).horizon_eq]
    exact lt_add_one _
  · exact RetainedCoreHistory.appendEventCompatible_of_time_eq_horizon _ _
      ((C.alignedLayer n).time_last_eq.trans (C.alignedLayer n).horizon_eq.symm)

private theorem alignedLayer_initial_map_heq (C : RetainedCoreEventChain P g) (n : ℕ) :
    HEq ((C.alignedLayer (n + 1)).initial.map) ((C.alignedLayer n).initial.map) := by
  exact InitialIdentification.map_of_stageZero_heq (C.alignedLayer n).initial
    (C.nextStageZero n (C.alignedLayer n)) (C.nextInitialMetricHeq n (C.alignedLayer n))

def toRetainedCoreObservationTower (C : RetainedCoreEventChain P g) :
    RetainedCoreObservationTower P g where
  history n := (C.alignedLayer n).history
  horizon_eq n := (C.alignedLayer n).horizon_eq
  initial n := (C.alignedLayer n).initial
  successor n := by
    have hpref := C.alignedLayer_prefix n
    have hsp := hpref.presentation
    have hpoint : (⟨(C.alignedLayer n).history.horizon,
        (C.alignedLayer n).history.horizon_nonneg, hpref.horizon_le⟩
        : Icc (0 : ℝ) (C.alignedLayer (n + 1)).history.horizon) =
        ⟨(n : ℝ), Nat.cast_nonneg n, by
          have h : (n : ℝ) ≤ (C.alignedLayer (n + 1)).history.horizon := by
            rw [(C.alignedLayer (n + 1)).horizon_eq]
            exact_mod_cast Nat.le_succ n
          simpa using h⟩ :=
      Subtype.ext (C.alignedLayer n).horizon_eq
    rw [hpoint] at hsp
    exact hsp
  initial_successor n :=
    (heq_of_eq (InitialIdentification.restrict_map (C.alignedLayer (n + 1)).initial
      ⟨(n : ℝ), Nat.cast_nonneg n, by
        have h : (n : ℝ) ≤ (C.alignedLayer (n + 1)).history.horizon := by
          rw [(C.alignedLayer (n + 1)).horizon_eq]
          exact_mod_cast Nat.le_succ n
        simpa using h⟩)).trans (C.alignedLayer_initial_map_heq n)

theorem toRetainedCoreObservationTower_history_eventCount (C : RetainedCoreEventChain P g)
    (n : ℕ) : (C.toRetainedCoreObservationTower.history n).eventCount = n :=
  (C.alignedLayer n).eventCount_eq

theorem toRetainedCoreObservationTower_history_stage_last (C : RetainedCoreEventChain P g)
    (n : ℕ) :
    (C.toRetainedCoreObservationTower.history n).stage
        (Fin.last (C.toRetainedCoreObservationTower.history n).eventCount) = C.stage n :=
  (C.alignedLayer n).stage_last_eq

theorem toRetainedCoreObservationTower_history_time_last_eq_horizon
    (C : RetainedCoreEventChain P g) (n : ℕ) :
    (C.toRetainedCoreObservationTower.history n).time
        (Fin.last (C.toRetainedCoreObservationTower.history n).eventCount) =
      (C.toRetainedCoreObservationTower.history n).horizon :=
  ((C.alignedLayer n).time_last_eq.trans (C.alignedLayer n).horizon_eq.symm)

end RetainedCoreEventChain

theorem hasSurgeryContinuationTower_of_retainedCoreEventChain {P : OrientedThreeStage.{u}}
    {g : P.Metric} (C : RetainedCoreEventChain P g)
    (hrecords : C.toRetainedCoreObservationTower.HasUniformCutoffRecords)
    (hbfr : C.toRetainedCoreObservationTower.hasBoundaryFrameReversing)
    (hctrl : C.toRetainedCoreObservationTower.hasPoincareStandardDiscarded) :
    HasSurgeryContinuationTower P g :=
  hasSurgeryContinuationTower_of_uniformCutoffRecords C.toRetainedCoreObservationTower
    hrecords hbfr hctrl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
