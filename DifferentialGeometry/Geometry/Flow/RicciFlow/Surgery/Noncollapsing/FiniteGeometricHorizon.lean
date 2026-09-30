import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.GeometricHorizons
namespace GC.GeneralFlow
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
set_option autoImplicit false
noncomputable section
universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private theorem prefix_stage_zero_eq {H K : ObservedHistory.{u}} (h : H.IsPrefixOf K) :
    K.stage 0 = H.stage 0 := by
  have hh := h.presentation.stage_eq 0
  simpa only [Fin.cast_zero, ObservedHistory.restrict_stage_zero] using hh

private theorem prefix_metric_zero_heq {H K : ObservedHistory.{u}} (h : H.IsPrefixOf K) :
    HEq (K.initialMetric 0) (H.initialMetric 0) := by
  have hh := h.presentation.initialMetric_heq 0
  simpa only [Fin.cast_zero, ObservedHistory.restrict_initialMetric_zero,
    ObservedHistory.restrict_stage_zero] using hh

theorem initial_scalar_barrier_for_stage
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ c : ℝ, 0 < c ∧ InitialScalarBarrier g c := by
  cases isEmpty_or_nonempty P.Carrier with
  | inl h =>
    let := h
    exact ⟨1,one_pos,fun x => isEmptyElim x⟩
  | inr h =>
    let := h
    exact exists_initialScalarBarrier_of_compact g

theorem finite_geometric_horizon_of_production
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hproduce : GeometricHorizonProduction P g) (B : ℝ) (hB : 0 < B) :
    ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
      (p : CutoffParameters), K.horizon = B ∧
      (InitialIdentification.atZero P g).IsPrefixOf A ∧
      Nonempty (∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p) ∧
      (∀ i : Fin K.eventCount, (K.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin K.eventCount, (K.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      ∀ i : Fin K.eventCount,
        GC.Surgery.ActualMetricEventGeometry (K.coreEvent i).toMetricCutCapEvent := by
  classical
  obtain ⟨c,hc,hscalar0⟩ := initial_scalar_barrier_for_stage P g
  obtain ⟨p₀,v,Inv,hv,hInv,hstep⟩ := hproduce B hB
  let H₀ := RetainedCoreHistory.atZero P g
  let S : Set (RetainedCoreHistory.{u}) := {H |
    H₀.toHistory.IsPrefixOf H.toHistory ∧ H.horizon ≤ B ∧
    H.time (Fin.last H.eventCount) = H.horizon ∧ Inv H ∧
    ∃ p : CutoffParameters,
      p.fixed = p₀.fixed ∧ p.modelRadius = p₀.modelRadius ∧
      p.modelOrder = p₀.modelOrder ∧ p.modelAccuracy = p₀.modelAccuracy ∧
      p.recenterConstant = p₀.recenterConstant ∧
      Nonempty (∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) ∧
      (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin H.eventCount,
        (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      ∀ i : Fin H.eventCount,
        ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
            (H.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
            (H.coreEvent i).terminal.metric F}
  have hzero : H₀ ∈ S := by
    refine ⟨ObservedHistory.IsPrefixOf.refl _, hB.le, rfl, hInv, p₀, rfl, rfl, rfl, rfl, rfl,
      ⟨fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  have hex : ∀ H ∈ S, ∃ p : CutoffParameters,
      p.fixed = p₀.fixed ∧ p.modelRadius = p₀.modelRadius ∧
      p.modelOrder = p₀.modelOrder ∧ p.modelAccuracy = p₀.modelAccuracy ∧
      p.recenterConstant = p₀.recenterConstant ∧
      Nonempty (∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) ∧
      (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin H.eventCount,
        (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      ∀ i : Fin H.eventCount,
        ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
            (H.coreEvent i).outputMetric univ +
              ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
            (H.coreEvent i).terminal.metric F := fun H hH => hH.2.2.2.2
  choose p hfixed hradius horder haccuracy hrecenter hrecords hbfr hctrl hdebit using hex
  have hclosed : ∀ H ∈ S, H.horizon < B →
      ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
        (H.time (Fin.last H.eventCount)) s), s ≤ B →
        G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) → G.SingularEndpoint →
        ∃ (Q : OrientedThreeStage.{u})
          (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
            (H.time (Fin.last H.eventCount)) s)
          (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
            (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount)),
          E.incoming = G ∧ H.appendEvent E.incoming.lt E hinit ∈ S := by
    intro H hH hHB s G hs hinit hsing
    let A := (InitialIdentification.atZero P g).ofStageZero
      (prefix_stage_zero_eq hH.1) (prefix_metric_zero_heq hH.1)
    obtain ⟨Q, E, hE, q, hincoming, hInvNext, hqfixed, hqradius, hqorder, hqaccuracy, hqrecenter,
      ⟨R⟩, hbfrE, hctrlE, hgeometryE, F, hF, hvol⟩ :=
      hstep H A hH.2.2.2.1 (p H hH) hH.2.2.1 hHB (hfixed H hH) (hradius H hH) (horder H hH)
        (haccuracy H hH) (hrecenter H hH) (Classical.choice (hrecords H hH))
        (hbfr H hH) (hctrl H hH) (hdebit H hH) s G hs hinit hsing
    refine ⟨Q, E, hE, hincoming, ?_⟩
    let K := H.appendEvent E.incoming.lt E hE
    have hp : H.toHistory.IsPrefixOf K.toHistory :=
      H.appendEvent_isPrefixOf E.incoming.lt E hE (hH.2.2.1 ▸ E.incoming.lt)
        (H.appendEventCompatible_of_time_eq_horizon E hH.2.2.1)
    refine ⟨hH.1.trans hp, hs, H.appendEvent_time_last E.incoming.lt E hE, hInvNext,
      (p H hH).spliceAt q s, hfixed H hH, hradius H hH, horder H hH,
      haccuracy H hH, hrecenter H hH, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hR := R.spliceParametersAt hqfixed hqradius hqorder hqaccuracy hqrecenter
        have ht : (H.appendEvent E.incoming.lt E hE).toHistory.time
            (Fin.last H.eventCount).succ = s :=
          H.appendEvent_time_last E.incoming.lt E hE
        exact Eq.mp (congrArg
          (fun q' => GeometricCutoffRecord (H.appendEvent E.incoming.lt E hE).toHistory
            (Fin.last H.eventCount) q') (congrArg ((p H hH).spliceAt q) ht)) hR
      · apply (GeometricCutoffRecord.appendEvent E.incoming.lt E hE
          (Classical.choice (hrecords H hH) j)).spliceParametersOfNe
        have ht : (H.appendEvent E.incoming.lt E hE).toHistory.time j.castSucc.succ =
            H.time j.succ := H.appendEvent_time_castSucc E.incoming.lt E hE j.succ
        intro heq
        exact (ne_of_lt ((H.time_strictMono.monotone (Fin.le_last j.succ)).trans_lt
          E.incoming.lt)) (ht.symm.trans heq)
    · intro i
      exact (H.appendEvent_boundaryFrameReversing_and_poincareStandardDiscarded
        E.incoming.lt E hE (hbfr H hH) (hctrl H hH) hbfrE hctrlE i).1
    · intro i
      exact (H.appendEvent_boundaryFrameReversing_and_poincareStandardDiscarded
        E.incoming.lt E hE (hbfr H hH) (hctrl H hH) hbfrE hctrlE i).2
    · exact H.appendEvent_compact_volume_debit E.incoming.lt E hE v
        (hdebit H hH) ⟨F, hF, hvol⟩
  have hscalar : ∀ K ∈ S, ∀ i : Fin K.eventCount,
      ∀ t ∈ Ico (K.time i.castSucc) (K.time i.succ),
      ∀ x : (K.stage i.castSucc).Carrier,
        -(3 / (2 * c)) ≤ metricScalarAt ((K.coreEvent i).incoming.flow.base.metric t) x := by
    intro K hK i t ht x
    let A' := (InitialIdentification.atZero P g).ofStageZero (prefix_stage_zero_eq hK.1)
      (prefix_metric_zero_heq hK.1)
    have hstage := DifferentialGeometry.PDE.RicciFlow.stageInitial_scalarLowerBound_of_history
      (Classical.choice (hrecords K hK)) hc (A'.stageZero_scalarLowerBound hscalar0)
    have hinit : ∀ y : (K.stage i.castSucc).Carrier,
        -3 / (2 * (K.time i.castSucc + c)) ≤
          metricScalarAt ((K.coreEvent i).incoming.flow.base.metric (K.time i.castSucc)) y := by
      intro y
      change -3 / (2 * (K.time i.castSucc + c)) ≤
        metricScalarAt ((K.coreEvent i).toMetricCutCapEvent.incoming.flow.base.metric
          (K.time i.castSucc)) y
      rw [K.event_initial i]
      exact hstage i.castSucc y
    have hbound := DifferentialGeometry.PDE.RicciFlow.incomingSlab_scalarLowerBarrier_le
      (K.toHistory.time_nonneg i.castSucc) hc (K.coreEvent i).incoming hinit ht x
    have ht0 : 0 ≤ t := (K.toHistory.time_nonneg i.castSucc).trans ht.1
    have hd : 3 / (2 * (t + c)) ≤ 3 / (2 * c) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have hneg : -(3 / (2 * c)) ≤ -3 / (2 * (t + c)) := by
      simpa only [neg_div] using neg_le_neg hd
    exact hneg.trans hbound
  obtain ⟨J,hJ,hJB | ⟨hJB,G,hG,hprefix⟩⟩ :=
    H₀.exists_closedSlab_extension_to_horizon_of_volume_debit S hzero
      (by positivity : 0 ≤ 3 / (2 * c)) hv
      (fun K hK => hK.1) (fun K hK => hK.2.1) (fun K hK => hK.2.2.1)
      hscalar hdebit hclosed
  · let A := (InitialIdentification.atZero P g).ofStageZero
      (prefix_stage_zero_eq hJ.1) (prefix_metric_zero_heq hJ.1)
    refine ⟨J,A,p J hJ,hJB,?_,hrecords J hJ,hbfr J hJ,hctrl J hJ,?_⟩
    · exact ⟨hJ.1,((InitialIdentification.atZero P g).map_of_stageZero_heq _ _).symm⟩
    · intro i
      exact GC.Surgery.actual_metric_event_geometry (J.coreEvent i).toMetricCutCapEvent
        (hbfr J hJ i) (hctrl J hJ i)
  · let K := J.extendHorizon B hJB G hG
    let A := (InitialIdentification.atZero P g).ofStageZero
      (prefix_stage_zero_eq hprefix) (prefix_metric_zero_heq hprefix)
    refine ⟨K,A,p J hJ,rfl,?_,?_,hbfr J hJ,hctrl J hJ,?_⟩
    · exact ⟨hprefix,((InitialIdentification.atZero P g).map_of_stageZero_heq _ _).symm⟩
    · refine ⟨fun i => ?_⟩
      exact GeometricCutoffRecord.extendHorizon B hJB G hG
        (Classical.choice (hrecords J hJ) i)
    · intro i
      exact GC.Surgery.actual_metric_event_geometry (K.coreEvent i).toMetricCutCapEvent
        (hbfr J hJ i) (hctrl J hJ i)

theorem finite_geometric_horizon
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hcn : CanonicalNeighborhoodsThroughSurgeryStrong P g) (B : ℝ) (hB : 0 < B) :
    ∃ (K : RetainedCoreHistory.{u}) (A : InitialIdentification P g K.toHistory)
      (p : CutoffParameters), K.horizon = B ∧
      (InitialIdentification.atZero P g).IsPrefixOf A ∧
      Nonempty (∀ i : Fin K.eventCount, GeometricCutoffRecord K.toHistory i p) ∧
      (∀ i : Fin K.eventCount, (K.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin K.eventCount, (K.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      ∀ i : Fin K.eventCount,
        GC.Surgery.ActualMetricEventGeometry (K.coreEvent i).toMetricCutCapEvent :=
  finite_geometric_horizon_of_production P g (geometric_horizon_production P g hcn) B hB

end
end GC.GeneralFlow
