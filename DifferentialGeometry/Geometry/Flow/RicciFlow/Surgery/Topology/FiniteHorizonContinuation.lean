import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryEventVolumeBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerBookkeeping

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private theorem prefix_initial_stage {H K : ObservedHistory.{u}} (h : H.IsPrefixOf K) :
    K.stage 0 = H.stage 0 := by
  have hh := h.presentation.stage_eq 0
  simpa only [Fin.cast_zero, ObservedHistory.restrict_stage_zero] using hh

private theorem prefix_initial_metric {H K : ObservedHistory.{u}} (h : H.IsPrefixOf K) :
    HEq (K.initialMetric 0) (H.initialMetric 0) := by
  have hh := h.presentation.initialMetric_heq 0
  simpa only [Fin.cast_zero, ObservedHistory.restrict_initialMetric_zero, ObservedHistory.restrict_stage_zero] using hh

private theorem prefix_initial_budget {H K : ObservedHistory.{u}} (h : H.IsPrefixOf K)
    (v C B : ℝ) :
    (Nat.card (ConnectedComponents (K.stage 0).Carrier) : ℝ) +
        2 * (Real.exp (C * B) *
          (riemannianVolumeMeasure ThreeModel (K.stage 0).Carrier
            (K.initialMetric 0) univ).toReal / v) =
      Nat.card (ConnectedComponents (H.stage 0).Carrier) +
        2 * (Real.exp (C * B) *
          (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
            (H.initialMetric 0) univ).toReal / v) := by
  let f := fun q : Sigma fun P : OrientedThreeStage.{u} => P.Metric =>
    (Nat.card (ConnectedComponents q.1.Carrier) : ℝ) +
      2 * (Real.exp (C * B) *
        (riemannianVolumeMeasure ThreeModel q.1.Carrier q.2 univ).toReal / v)
  have hpair : (⟨K.stage 0, K.initialMetric 0⟩ : Sigma fun P : OrientedThreeStage.{u} => P.Metric) =
      ⟨H.stage 0, H.initialMetric 0⟩ :=
    Sigma.ext (prefix_initial_stage h) (prefix_initial_metric h)
  change f ⟨K.stage 0, K.initialMetric 0⟩ = f ⟨H.stage 0, H.initialMetric 0⟩
  exact congrArg f hpair


theorem RetainedCoreHistory.exists_closedSlab_extension_to_horizon_of_volume_debit
    (H : RetainedCoreHistory.{u})
    (S : Set (RetainedCoreHistory.{u})) (hH : H ∈ S)
    {B C v : ℝ} (hC : 0 ≤ C) (hv : 0 < v)
    (hprefix : ∀ K ∈ S, H.toHistory.IsPrefixOf K.toHistory)
    (hhorizon : ∀ K ∈ S, K.horizon ≤ B)
    (hend : ∀ K ∈ S, K.time (Fin.last K.eventCount) = K.horizon)
    (hscalar : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      ∀ t ∈ Ico (K.time i.castSucc) (K.time i.succ),
      ∀ x : (K.stage i.castSucc).Carrier,
        -C ≤ metricScalarAt ((K.coreEvent i).incoming.flow.base.metric t) x)
    (hdebit : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
          (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
          (K.coreEvent i).terminal.metric F)
    (hproduce : ∀ K ∈ S, K.horizon < B →
      ∀ (s : ℝ) (G : (K.stage (Fin.last K.eventCount)).IncomingSlab
        (K.time (Fin.last K.eventCount)) s),
      s ≤ B →
      G.flow.base.metric (K.time (Fin.last K.eventCount)) =
        K.initialMetric (Fin.last K.eventCount) → G.SingularEndpoint →
      ∃ (Q : OrientedThreeStage.{u})
        (E : RetainedCoreEvent (K.stage (Fin.last K.eventCount)) Q
          (K.time (Fin.last K.eventCount)) s)
        (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
          (K.time (Fin.last K.eventCount)) = K.initialMetric (Fin.last K.eventCount)),
        E.incoming = G ∧ K.appendEvent E.incoming.lt E hinit ∈ S) :
    ∃ J ∈ S, J.horizon = B ∨
      ∃ (hB : J.horizon ≤ B)
        (G : (J.stage (Fin.last J.eventCount)).ClosedSlab
          (J.time (Fin.last J.eventCount)) B)
        (hG : G.flow.base.metric (J.time (Fin.last J.eventCount)) =
          J.initialMetric (Fin.last J.eventCount)),
        H.toHistory.IsPrefixOf (J.extendHorizon B hB G hG).toHistory := by
  classical
  let budget : ℝ := Nat.card (ConnectedComponents (H.stage 0).Carrier) +
    2 * (Real.exp (C * B) *
      (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
        (H.initialMetric 0) univ).toReal / v)
  have hbound : ∀ K ∈ S, (K.eventCount : ℝ) ≤ budget := by
    intro K hK
    have h := K.toHistory.eventCount_le_card_initial_add_volume_bound hv hC
      (hhorizon K hK) (hscalar K hK) (hdebit K hK)
    rw [prefix_initial_budget (hprefix K hK) v C B] at h
    exact h
  have hfinite : (RetainedCoreHistory.eventCount '' S).Finite := by
    apply (Set.finite_Iic ⌈budget⌉₊).subset
    rintro n ⟨K, hK, rfl⟩
    exact_mod_cast (hbound K hK).trans (Nat.le_ceil budget)
  obtain ⟨n, hn, hmax⟩ := Set.exists_max_image
    (RetainedCoreHistory.eventCount '' S) id hfinite ⟨H.eventCount, H, hH, rfl⟩
  obtain ⟨K, hK, rfl⟩ := hn
  have hmaxK : ∀ L ∈ S, L.eventCount ≤ K.eventCount :=
    fun L hL => hmax _ ⟨L, hL, rfl⟩
  rcases eq_or_lt_of_le (hhorizon K hK) with heq | hlt
  · exact ⟨K, hK, Or.inl heq⟩
  obtain ⟨G, hinit⟩ | ⟨s, G, hs, hinit, hsing⟩ :=
    (K.stage (Fin.last K.eventCount)).exists_closedSlab_or_singular_incomingSlab_from_time
      (K.initialMetric (Fin.last K.eventCount)) ((hend K hK).trans_lt hlt)
  · refine ⟨K, hK, Or.inr ⟨hlt.le, G, hinit, ?_⟩⟩
    exact (hprefix K hK).trans (K.extendHorizon_isPrefixOf_of_time_eq_horizon
      B hlt.le G hinit (hend K hK))
  · obtain ⟨Q, E, hE, _, hmem⟩ := hproduce K hK hlt s G hs hinit hsing
    have hcount := hmaxK (K.appendEvent E.incoming.lt E hE) hmem
    change K.eventCount + 1 ≤ K.eventCount at hcount
    omega

theorem RetainedCoreHistory.exists_extension_to_horizon_of_volume_debit
    {P : OrientedThreeStage.{u}} {g : P.Metric} (H : RetainedCoreHistory.{u})
    (A : InitialIdentification P g H.toHistory)
    (S : Set (RetainedCoreHistory.{u})) (hH : H ∈ S)
    {B C v : ℝ} (hC : 0 ≤ C) (hv : 0 < v)
    (hprefix : ∀ K ∈ S, H.toHistory.IsPrefixOf K.toHistory)
    (hhorizon : ∀ K ∈ S, K.horizon ≤ B)
    (hend : ∀ K ∈ S, K.time (Fin.last K.eventCount) = K.horizon)
    (hscalar : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      ∀ t ∈ Ico (K.time i.castSucc) (K.time i.succ),
      ∀ x : (K.stage i.castSucc).Carrier,
        -C ≤ metricScalarAt ((K.coreEvent i).incoming.flow.base.metric t) x)
    (hdebit : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      ∃ F : Set (K.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
          (K.coreEvent i).outputMetric univ +
            ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
          (K.coreEvent i).terminal.metric F)
    (hproduce : ∀ K ∈ S, K.horizon < B →
      ∀ (s : ℝ) (G : (K.stage (Fin.last K.eventCount)).IncomingSlab
        (K.time (Fin.last K.eventCount)) s),
      s ≤ B →
      G.flow.base.metric (K.time (Fin.last K.eventCount)) =
        K.initialMetric (Fin.last K.eventCount) → G.SingularEndpoint →
      ∃ (Q : OrientedThreeStage.{u})
        (E : RetainedCoreEvent (K.stage (Fin.last K.eventCount)) Q
          (K.time (Fin.last K.eventCount)) s)
        (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
          (K.time (Fin.last K.eventCount)) = K.initialMetric (Fin.last K.eventCount)),
        E.incoming = G ∧ K.appendEvent E.incoming.lt E hinit ∈ S) :
    ∃ (K : RetainedCoreHistory.{u}) (A' : InitialIdentification P g K.toHistory),
      K.horizon = B ∧ A.IsPrefixOf A' ∧
      ∃ J ∈ S, J.toHistory.IsPrefixOf K.toHistory ∧ K.eventCount = J.eventCount := by
  classical
  obtain ⟨J, hJ, hJB | ⟨hB, G, hG, hp⟩⟩ :=
    H.exists_closedSlab_extension_to_horizon_of_volume_debit S hH hC hv hprefix hhorizon
      hend hscalar hdebit hproduce
  · let A' := A.ofStageZero (prefix_initial_stage (hprefix J hJ))
      (prefix_initial_metric (hprefix J hJ))
    refine ⟨J, A', hJB, ⟨hprefix J hJ, ?_⟩,
      J, hJ, ObservedHistory.IsPrefixOf.refl _, rfl⟩
    exact (A.map_of_stageZero_heq _ _).symm
  · let K := J.extendHorizon B hB G hG
    let A' := A.ofStageZero (prefix_initial_stage hp) (prefix_initial_metric hp)
    exact ⟨K, A', rfl, ⟨hp, (A.map_of_stageZero_heq _ _).symm⟩,
      J, hJ, J.extendHorizon_isPrefixOf_of_time_eq_horizon B hB G hG (hend J hJ), rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
