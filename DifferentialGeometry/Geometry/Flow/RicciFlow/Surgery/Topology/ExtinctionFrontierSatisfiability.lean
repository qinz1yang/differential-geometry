import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctObservationNucleus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreExtinctionLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCap

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem ObservedHistory.not_isEmpty_stage_of_ne_last (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) (hj : j ≠ Fin.last H.eventCount) :
    ¬ IsEmpty (H.stage j).Carrier := by
  intro h
  exact hj (letI := h; ObservedHistory.empty_stage_is_last H j)

theorem ObservedHistory.nonempty_stage_of_ne_last (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) (hj : j ≠ Fin.last H.eventCount) :
    Nonempty (H.stage j).Carrier :=
  not_isEmpty_iff.mp (ObservedHistory.not_isEmpty_stage_of_ne_last H j hj)

theorem MetricCutCapEvent.nonempty_discarded_of_isEmpty_output
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (hQ : IsEmpty Q.Carrier) : Nonempty E.discarded.Carrier :=
  E.transition.nonempty_output_piece.resolve_left fun h => hQ.false h.some

theorem RetainedCoreEvent.nonempty_discarded_of_isEmpty_output
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s)
    (hQ : IsEmpty Q.Carrier) : Nonempty E.discarded.Carrier :=
  E.transition.nonempty_output_piece.resolve_left fun h => hQ.false h.some

theorem ObservedHistory.exists_extinctionEvent_of_isExtinctAtHorizon (H : ObservedHistory.{u})
    [Nonempty (H.stage 0).Carrier] (hempty : H.IsExtinctAtHorizon) :
    ∃ i : Fin H.eventCount, i.succ = Fin.last H.eventCount ∧
      Nonempty (H.stage i.castSucc).Carrier ∧ IsEmpty (H.stage i.succ).Carrier ∧
      Nonempty (H.event i).discarded.Carrier := by
  have hlast : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := hempty
  have hn : 0 < H.eventCount := @ObservedHistory.eventCount_pos_of_final_empty H _ hlast
  let i : Fin H.eventCount := ⟨H.eventCount - 1, by omega⟩
  have hsucc : i.succ = Fin.last H.eventCount := by
    apply Fin.ext
    change H.eventCount - 1 + 1 = H.eventCount
    omega
  refine ⟨i, hsucc, H.incoming_nonempty i, ?_, ?_⟩
  · rw [hsucc]
    exact hempty
  · exact (H.event i).nonempty_discarded_of_isEmpty_output (by rw [hsucc]; exact hempty)

theorem HasExtinctRetainedCoreHistory.exists_extinctionEvent
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistory M g) :
    ∃ (H : RetainedCoreHistory.{u})
      (_ : InitialIdentification
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory)
      (i : Fin H.eventCount),
      i.succ = Fin.last H.eventCount ∧
      Nonempty (H.stage i.castSucc).Carrier ∧
      IsEmpty (H.stage i.succ).Carrier ∧
      Nonempty (H.coreEvent i).discarded.Carrier ∧
      (H.coreEvent i).transition.boundaryFrameReversing ∧
      (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded := by
  obtain ⟨H, A, hbfr, hctrl, hempty⟩ := h
  have : Nonempty (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := M.connected.toNonempty
  have : Nonempty (H.toHistory.stage 0).Carrier := A.initial_nonempty
  obtain ⟨i, hsucc, hsrc, hsink, hdisc⟩ :=
    ObservedHistory.exists_extinctionEvent_of_isExtinctAtHorizon H.toHistory hempty
  exact ⟨H, A, i, hsucc, hsrc, hsink, hdisc, hbfr i, hctrl i⟩

theorem HasExtinctRetainedCoreHistory.exists_extinctionEvent_discardedStandard
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistory M g) :
    ∃ (H : RetainedCoreHistory.{u})
      (_ : InitialIdentification
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory)
      (i : Fin H.eventCount) (q : ConnectedComponents (H.coreEvent i).discarded.Carrier),
      i.succ = Fin.last H.eventCount ∧
      Nonempty (H.stage i.castSucc).Carrier ∧
      IsEmpty (H.stage i.succ).Carrier ∧
      Nonempty (H.coreEvent i).discarded.Carrier ∧
      (H.coreEvent i).transition.boundaryFrameReversing ∧
      Nonempty ((H.coreEvent i).discarded.toClosedOrientedManifold.component q).Carrier ∧
      DifferentialGeometry.Topology.isPoincareStandard
        ((H.coreEvent i).discarded.toClosedOrientedManifold.component q).Carrier := by
  obtain ⟨H, A, i, hsucc, hsrc, hsink, hdisc, hbfr, hctrl⟩ := h.exists_extinctionEvent M g
  obtain ⟨d⟩ := hdisc
  exact ⟨H, A, i, ConnectedComponents.mk d, hsucc, hsrc, hsink, ⟨d⟩, hbfr,
    ⟨⟨d, rfl⟩⟩, hctrl (ConnectedComponents.mk d)⟩

theorem HasExtinctObservationNucleus.exists_extinctionEvent
    {P : OrientedThreeStage.{u}} {g : P.Metric} [Nonempty P.Carrier]
    (h : HasExtinctObservationNucleus P g) :
    ∃ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H) (i : Fin H.eventCount),
      i.succ = Fin.last H.eventCount ∧
      Nonempty (H.stage i.castSucc).Carrier ∧
      IsEmpty (H.stage i.succ).Carrier ∧
      Nonempty (H.event i).discarded.Carrier ∧
      (H.event i).transition.boundaryFrameReversing ∧
      (H.event i).coreInclusionIsSmoothEmbedding ∧
      (H.event i).poincareStandardDiscarded := by
  obtain ⟨H, A, hbfr, hcore, hctrl, hempty⟩ := h
  have : Nonempty (H.stage 0).Carrier := A.initial_nonempty
  obtain ⟨i, hsucc, hsrc, hsink, hdisc⟩ :=
    ObservedHistory.exists_extinctionEvent_of_isExtinctAtHorizon H hempty
  exact ⟨H, A, i, hsucc, hsrc, hsink, hdisc, hbfr i, hcore i, hctrl i⟩

theorem HasExtinctObservationNucleusWithCompletion.exists_extinctionEvent
    {P : OrientedThreeStage.{u}} {g : P.Metric} [Nonempty P.Carrier]
    (h : HasExtinctObservationNucleusWithCompletion P g) :
    ∃ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H) (i : Fin H.eventCount),
      i.succ = Fin.last H.eventCount ∧
      Nonempty (H.stage i.castSucc).Carrier ∧
      IsEmpty (H.stage i.succ).Carrier ∧
      Nonempty (H.event i).discarded.Carrier ∧
      (H.event i).transition.boundaryFrameReversing ∧
      (H.event i).hasCutCapCompletion ∧
      (H.event i).coreInclusionIsSmoothEmbedding ∧
      (H.event i).poincareStandardDiscarded := by
  obtain ⟨H, A, hbfr, hcomp, hcore, hctrl, hempty⟩ := h
  have : Nonempty (H.stage 0).Carrier := A.initial_nonempty
  obtain ⟨i, hsucc, hsrc, hsink, hdisc⟩ :=
    ObservedHistory.exists_extinctionEvent_of_isExtinctAtHorizon H hempty
  exact ⟨H, A, i, hsucc, hsrc, hsink, hdisc, hbfr i, hcomp i, hcore i, hctrl i⟩

theorem HasExtinctObservationNucleusOfCutCapCompletion.exists_extinctionEvent
    {P : OrientedThreeStage.{u}} {g : P.Metric} [Nonempty P.Carrier]
    (h : HasExtinctObservationNucleusOfCutCapCompletion P g) :
    ∃ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H) (i : Fin H.eventCount),
      i.succ = Fin.last H.eventCount ∧
      Nonempty (H.stage i.castSucc).Carrier ∧
      IsEmpty (H.stage i.succ).Carrier ∧
      Nonempty (H.event i).discarded.Carrier ∧
      (H.event i).hasCutCapCompletion ∧
      (H.event i).coreInclusionIsSmoothEmbedding ∧
      (H.event i).poincareStandardDiscarded := by
  obtain ⟨H, A, hcomp, hcore, hctrl, hempty⟩ := h
  have : Nonempty (H.stage 0).Carrier := A.initial_nonempty
  obtain ⟨i, hsucc, hsrc, hsink, hdisc⟩ :=
    ObservedHistory.exists_extinctionEvent_of_isExtinctAtHorizon H hempty
  exact ⟨H, A, i, hsucc, hsrc, hsink, hdisc, hcomp i, hcore i, hctrl i⟩

theorem HasExtinctStandardSideNucleus.exists_extinctionEvent
    {P : OrientedThreeStage.{u}} {g : P.Metric} [Nonempty P.Carrier]
    (h : HasExtinctStandardSideNucleus P g) :
    ∃ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H) (i : Fin H.eventCount),
      i.succ = Fin.last H.eventCount ∧
      Nonempty (H.stage i.castSucc).Carrier ∧
      IsEmpty (H.stage i.succ).Carrier ∧
      Nonempty (H.event i).discarded.Carrier ∧
      (H.event i).transition.boundaryFrameReversing ∧
      (H.event i).coreInclusionIsSmoothEmbedding ∧
      (H.event i).discarded.toClosedOrientedManifold.componentwiseStandardFactor := by
  obtain ⟨H, A, hbfr, hcore, hside, hempty⟩ := h
  have : Nonempty (H.stage 0).Carrier := A.initial_nonempty
  obtain ⟨i, hsucc, hsrc, hsink, hdisc⟩ :=
    ObservedHistory.exists_extinctionEvent_of_isExtinctAtHorizon H hempty
  exact ⟨H, A, i, hsucc, hsrc, hsink, hdisc, hbfr i, hcore i, hside i⟩

theorem HasExtinctRetainedCoreHistoryAtTime.exists_extinctionEvent
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistoryAtTime M g) :
    ∃ (H : RetainedCoreHistory.{u})
      (_ : InitialIdentification
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory)
      (t : Icc (0 : ℝ) H.horizon)
      (i : Fin (H.toHistory.restrict t).eventCount),
      i.succ = Fin.last (H.toHistory.restrict t).eventCount ∧
      Nonempty ((H.toHistory.restrict t).stage i.castSucc).Carrier ∧
      IsEmpty ((H.toHistory.restrict t).stage i.succ).Carrier ∧
      Nonempty ((H.toHistory.restrict t).event i).discarded.Carrier ∧
      (∀ j : Fin H.eventCount, (H.coreEvent j).transition.boundaryFrameReversing) ∧
      (∀ j : Fin H.eventCount,
        (H.coreEvent j).toMetricCutCapEvent.poincareStandardDiscarded) := by
  obtain ⟨H, A, t, hbfr, hctrl, hext⟩ := h
  have : Nonempty (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := M.connected.toNonempty
  have h0 : Nonempty ((H.toHistory.restrict t).stage 0).Carrier := by
    rw [ObservedHistory.restrict_stage_zero]
    exact A.initial_nonempty
  obtain ⟨i, hsucc, hsrc, hsink, hdisc⟩ :=
    @ObservedHistory.exists_extinctionEvent_of_isExtinctAtHorizon (H.toHistory.restrict t) h0 hext
  exact ⟨H, A, t, i, hsucc, hsrc, hsink, hdisc, hbfr, hctrl⟩

theorem HasExtinctRetainedCoreTower.exists_extinctionEvent
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreTower M g) :
    ∃ (T : RetainedCoreObservationTower
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
      (n : ℕ) (_ : 0 < n) (i : Fin (T.history n).toHistory.eventCount),
      i.succ = Fin.last (T.history n).toHistory.eventCount ∧
      Nonempty ((T.history n).toHistory.stage i.castSucc).Carrier ∧
      IsEmpty ((T.history n).toHistory.stage i.succ).Carrier ∧
      Nonempty ((T.history n).toHistory.event i).discarded.Carrier ∧
      (∀ (m : ℕ) (j : Fin (T.history m).eventCount),
        ((T.history m).coreEvent j).transition.boundaryFrameReversing) ∧
      (∀ (m : ℕ) (j : Fin (T.history m).eventCount),
        ((T.history m).coreEvent j).toMetricCutCapEvent.poincareStandardDiscarded) := by
  obtain ⟨T, hbfr, hctrl, n, hn, hext⟩ := h
  have : Nonempty (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := M.connected.toNonempty
  have h0 : Nonempty ((T.history n).toHistory.stage 0).Carrier := (T.initial n).initial_nonempty
  obtain ⟨i, hsucc, hsrc, hsink, hdisc⟩ :=
    @ObservedHistory.exists_extinctionEvent_of_isExtinctAtHorizon
      ((T.history n).toHistory) h0 hext
  exact ⟨T, n, hn, i, hsucc, hsrc, hsink, hdisc, hbfr, hctrl⟩

namespace RetainedCoreEvent

def extinctionHistory {P Q : OrientedThreeStage.{u}} {s : ℝ} (hs : 0 < s)
    (E : RetainedCoreEvent P Q 0 s) : RetainedCoreHistory.{u} where
  horizon := s
  horizon_nonneg := hs.le
  eventCount := 1
  time := Fin.cons 0 (fun _ : Fin 1 => s)
  time_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  time_zero := rfl
  time_le_horizon := le_rfl
  stage := Fin.cons P (fun _ : Fin 1 => Q)
  initialMetric := Fin.cons (E.incoming.flow.base.metric 0) (fun _ : Fin 1 => E.outputMetric)
  coreEvent := Fin.cons E (fun i : Fin 0 => Fin.elim0 i)
  event_initial := by
    intro i
    fin_cases i
    rfl
  event_output := by
    intro i
    fin_cases i
    rfl
  finalSlab := fun h => absurd h (lt_irrefl s)
  final_initial := fun h => absurd h (lt_irrefl s)

theorem extinctionHistory_stage_last {P Q : OrientedThreeStage.{u}} {s : ℝ} (hs : 0 < s)
    (E : RetainedCoreEvent P Q 0 s) :
    (extinctionHistory hs E).stage (Fin.last (extinctionHistory hs E).eventCount) = Q := rfl

end RetainedCoreEvent

theorem hasExtinctRetainedCoreHistory_of_extinctionEvent
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    {Q : OrientedThreeStage.{u}} {s : ℝ} (hs : 0 < s) (hQ : IsEmpty Q.Carrier)
    (E : RetainedCoreEvent
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) Q 0 s)
    (hm : E.incoming.flow.base.metric 0 = g)
    (hbfr : E.transition.boundaryFrameReversing)
    (hctrl : E.toMetricCutCapEvent.poincareStandardDiscarded) :
    HasExtinctRetainedCoreHistory M g := by
  refine ⟨RetainedCoreEvent.extinctionHistory hs E, ?_, ?_, ?_, ?_⟩
  · refine ⟨Diffeomorph.refl ThreeModel _ ∞, preservesTangentOrientation_refl _, ?_⟩
    intro x v w
    change (E.incoming.flow.base.metric 0).inner x
      (mfderiv ThreeModel ThreeModel (id : _ → _) x v)
      (mfderiv ThreeModel ThreeModel (id : _ → _) x w) = g.inner x v w
    rw [mfderiv_id, hm]
    rfl
  · intro i
    fin_cases i
    exact hbfr
  · intro i
    fin_cases i
    exact hctrl
  · exact hQ

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
