import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreExtinctHistory
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinctionLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinctionHorizon

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

theorem exists_restrict_isExtinctAtHorizon_of_isExtinctAtHorizon (H : ObservedHistory.{u})
    (h : H.IsExtinctAtHorizon) :
    ∃ t : Icc (0 : ℝ) H.horizon, (H.restrict t).IsExtinctAtHorizon := by
  refine ⟨⟨H.horizon, H.horizon_nonneg, le_rfl⟩, ?_⟩
  rw [IsExtinctAtHorizon] at h ⊢
  have hstage : (H.restrict ⟨H.horizon, H.horizon_nonneg, le_rfl⟩).stage
      (Fin.last (H.restrict ⟨H.horizon, H.horizon_nonneg, le_rfl⟩).eventCount) =
      H.stage (Fin.last H.eventCount) := by
    rw [← H.activeStage_at_horizon]
    rfl
  rwa [hstage]

theorem not_restrict_zero_isExtinctAtHorizon {P : OrientedThreeStage.{u}} {g : P.Metric}
    (H : ObservedHistory.{u}) (A : InitialIdentification P g H) [Nonempty P.Carrier] :
    ¬ (H.restrict ⟨0, le_rfl, H.horizon_nonneg⟩).IsExtinctAtHorizon := by
  intro h
  have hzero : H.activeStage ⟨0, le_rfl, H.horizon_nonneg⟩ = 0 := by
    have h0 := H.activeStage_at_time (0 : Fin (H.eventCount + 1))
    simpa [H.time_zero] using h0
  have hcount : (H.restrict ⟨0, le_rfl, H.horizon_nonneg⟩).eventCount = 0 := by
    rw [ObservedHistory.restrict_eventCount]
    exact congrArg Fin.val hzero
  have hlast : Fin.last (H.restrict ⟨0, le_rfl, H.horizon_nonneg⟩).eventCount =
      (0 : Fin ((H.restrict ⟨0, le_rfl, H.horizon_nonneg⟩).eventCount + 1)) :=
    Fin.ext (by simpa using hcount)
  rw [IsExtinctAtHorizon, hlast] at h
  have hne : Nonempty ((H.restrict ⟨0, le_rfl, H.horizon_nonneg⟩).stage 0).Carrier := by
    rw [ObservedHistory.restrict_stage_zero]
    exact A.initial_nonempty
  exact hne.elim h.false

end ObservedHistory

namespace RetainedCoreHistory

theorem exists_restrict_isExtinctAtHorizon_of_isExtinctAtHorizon (H : RetainedCoreHistory.{u})
    (h : H.toHistory.IsExtinctAtHorizon) :
    ∃ t : Icc (0 : ℝ) H.horizon, (H.toHistory.restrict t).IsExtinctAtHorizon :=
  H.toHistory.exists_restrict_isExtinctAtHorizon_of_isExtinctAtHorizon h

end RetainedCoreHistory

def HasExtinctRetainedCoreHistoryAtTime
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) : Prop :=
  ∃ (H : RetainedCoreHistory.{u})
    (_ : InitialIdentification
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory)
    (t : Icc (0 : ℝ) H.horizon),
    (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
    (∀ i : Fin H.eventCount,
      (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
    (H.toHistory.restrict t).IsExtinctAtHorizon

theorem hasExtinctRetainedCoreHistory_of_hasExtinctRetainedCoreHistoryAtTime
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistoryAtTime M g) : HasExtinctRetainedCoreHistory M g := by
  obtain ⟨H, A, t, hbfr, hctrl, hext⟩ := h
  exact ⟨H, A, hbfr, hctrl,
    ObservedHistory.isEmpty_stage_last_of_restrict_last (H := H.toHistory) t hext⟩

theorem hasExtinctRetainedCoreHistoryAtTime_of_hasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistory M g) : HasExtinctRetainedCoreHistoryAtTime M g := by
  obtain ⟨H, A, hbfr, hctrl, hempty⟩ := h
  obtain ⟨t, ht⟩ := H.exists_restrict_isExtinctAtHorizon_of_isExtinctAtHorizon hempty
  exact ⟨H, A, t, hbfr, hctrl, ht⟩

theorem hasExtinctRetainedCoreHistoryAtTime_iff_hasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    HasExtinctRetainedCoreHistoryAtTime M g ↔ HasExtinctRetainedCoreHistory M g :=
  ⟨hasExtinctRetainedCoreHistory_of_hasExtinctRetainedCoreHistoryAtTime M g,
    hasExtinctRetainedCoreHistoryAtTime_of_hasExtinctRetainedCoreHistory M g⟩

namespace RetainedCoreObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

def HasExtinctionLevel (T : RetainedCoreObservationTower P g) : Prop :=
  ∃ n : ℕ, 0 < n ∧ (T.history n).toHistory.IsExtinctAtHorizon

theorem towerExtinct_toObservationTower_of_hasExtinctionLevel
    (T : RetainedCoreObservationTower P g) (h : T.HasExtinctionLevel) :
    towerExtinct T.toObservationTower := by
  obtain ⟨n, hn, hext⟩ := h
  refine (ObservationTower.towerExtinct_iff_exists_extinct_level T.toObservationTower).mpr
    ⟨n, hn, ?_⟩
  exact (ObservedHistory.isExtinctAtHorizon_iff_of_samePresentation
    (ObservationTower.observe_eq_history T.toObservationTower n)).mpr hext

theorem hasExtinctionLevel_of_towerExtinct (T : RetainedCoreObservationTower P g)
    (h : towerExtinct T.toObservationTower) : T.HasExtinctionLevel := by
  obtain ⟨n, hn, hext⟩ := (ObservationTower.towerExtinct_iff_exists_extinct_level
    T.toObservationTower).mp h
  exact ⟨n, hn, (ObservedHistory.isExtinctAtHorizon_iff_of_samePresentation
    (ObservationTower.observe_eq_history T.toObservationTower n)).mp hext⟩

theorem hasExtinctionLevel_iff_towerExtinct (T : RetainedCoreObservationTower P g) :
    T.HasExtinctionLevel ↔ towerExtinct T.toObservationTower :=
  ⟨T.towerExtinct_toObservationTower_of_hasExtinctionLevel,
    T.hasExtinctionLevel_of_towerExtinct⟩

theorem hasExtinctionLevel_iff_exists_extinctByLevelWithin
    (T : RetainedCoreObservationTower P g) :
    T.HasExtinctionLevel ↔ ∃ B : ℝ, T.toObservationTower.ExtinctByLevelWithin B := by
  constructor
  · rintro ⟨n, hn, hext⟩
    exact ⟨(n : ℝ), n, hn, le_rfl, hext⟩
  · rintro ⟨_B, n, hn, _hnB, hext⟩
    exact ⟨n, hn, hext⟩

theorem hasExtinctionLevel_of_extinctAbove (T : RetainedCoreObservationTower P g) {B : ℝ}
    (h : T.toObservationTower.ExtinctAbove B) : T.HasExtinctionLevel :=
  T.hasExtinctionLevel_of_towerExtinct
    (ObservationTower.towerExtinct_of_extinctAbove T.toObservationTower h)

theorem hasExtinctionLevel_of_uniformRecordsAbove (T : RetainedCoreObservationTower P g)
    {c A : ℝ} (h : T.toObservationTower.UniformRecordsAbove c A) : T.HasExtinctionLevel :=
  T.hasExtinctionLevel_of_towerExtinct
    (ObservationTower.towerExtinct_of_uniformRecordsAbove T.toObservationTower h)

theorem hasExtinctionLevel_empty (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier]
    (g : P.Metric) : (empty P g).HasExtinctionLevel :=
  (empty P g).hasExtinctionLevel_of_towerExtinct (towerExtinct_empty P g)

theorem not_history_zero_isExtinctAtHorizon (T : RetainedCoreObservationTower P g)
    [Nonempty P.Carrier] : ¬ (T.history 0).toHistory.IsExtinctAtHorizon := by
  intro h
  have hcount : (T.history 0).toHistory.eventCount = 0 :=
    ObservedHistory.eventCount_eq_zero_of_horizon_zero (T.history 0).toHistory
      (by simpa using T.horizon_eq 0)
  have hlast : Fin.last (T.history 0).toHistory.eventCount =
      (0 : Fin ((T.history 0).toHistory.eventCount + 1)) :=
    Fin.ext (by simpa using hcount)
  rw [ObservedHistory.IsExtinctAtHorizon, hlast] at h
  exact h.false (T.initial 0).initial_nonempty.some

end RetainedCoreObservationTower

def HasExtinctRetainedCoreTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) : Prop :=
  ∃ T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g,
    T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧ T.HasExtinctionLevel

theorem hasExtinctRetainedCoreHistory_of_hasExtinctRetainedCoreTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreTower M g) : HasExtinctRetainedCoreHistory M g := by
  obtain ⟨T, hbfr, hctrl, hlevel⟩ := h
  exact RetainedCoreObservationTower.hasExtinctRetainedCoreHistory M T hbfr hctrl
    (T.towerExtinct_toObservationTower_of_hasExtinctionLevel hlevel)

theorem hasExtinctObservationTower_of_hasExtinctRetainedCoreTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreTower M g) : hasExtinctObservationTower M g := by
  obtain ⟨T, hbfr, hctrl, hlevel⟩ := h
  exact DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_cutCap
    M g T hbfr hctrl (T.towerExtinct_toObservationTower_of_hasExtinctionLevel hlevel)

theorem exists_pos_hasControlledExtinctionWithin_of_hasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistory M g) :
    ∃ B : ℝ, 0 < B ∧ HasControlledExtinctionWithin M.toClosedOrientedManifold g B := by
  obtain ⟨H, A, hbfr, hctrl, hempty⟩ := h
  have hcarrier : Nonempty (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := M.connected.toNonempty
  have hn : 0 < H.eventCount := H.eventCount_pos_of_final_empty A hempty
  refine ⟨H.time (Fin.last H.eventCount),
    ObservedHistory.last_time_pos (H := H.toHistory) hn, ?_⟩
  exact DifferentialGeometry.PDE.RicciFlow.Surgery.hasControlledExtinctionWithin_of_observedHistory
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory A
    (fun i => ((H.coreEvent i).toMetricCutCapEvent_hasCutCapCompletion (hbfr i)).some)
    (fun i => (H.coreEvent i).toMetricCutCapEvent_coreInclusionIsSmoothEmbedding)
    (fun i => hctrl i) hempty le_rfl

theorem exists_pos_hasControlledExtinctionWithin_of_hasExtinctRetainedCoreTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreTower M g) :
    ∃ B : ℝ, 0 < B ∧ HasControlledExtinctionWithin M.toClosedOrientedManifold g B :=
  exists_pos_hasControlledExtinctionWithin_of_hasExtinctRetainedCoreHistory M g
    (hasExtinctRetainedCoreHistory_of_hasExtinctRetainedCoreTower M g h)

theorem not_atZero_toHistory_isExtinctAtHorizon (P : OrientedThreeStage.{u}) [Nonempty P.Carrier]
    (g : P.Metric) : ¬ (RetainedCoreHistory.atZero P g).toHistory.IsExtinctAtHorizon := by
  intro h
  have hstage : (RetainedCoreHistory.atZero P g).toHistory.stage
      (Fin.last (RetainedCoreHistory.atZero P g).toHistory.eventCount) = P := rfl
  rw [ObservedHistory.IsExtinctAtHorizon, hstage] at h
  exact h.false (inferInstance : Nonempty P.Carrier).some

theorem not_exists_history_zero_isExtinctAtHorizon_atTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    ¬ (∃ T : RetainedCoreObservationTower
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g,
      T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧
        (T.history 0).toHistory.IsExtinctAtHorizon) := by
  have hcarrier : Nonempty (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := M.connected.toNonempty
  rintro ⟨T, _, _, h⟩
  exact T.not_history_zero_isExtinctAtHorizon h

theorem exists_retainedCoreHistory_extinctAtTime_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) :
    ∃ (H : RetainedCoreHistory.{u}) (_ : InitialIdentification P g H.toHistory)
      (t : Icc (0 : ℝ) H.horizon),
      (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin H.eventCount,
        (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      (H.toHistory.restrict t).IsExtinctAtHorizon := by
  obtain ⟨n, _hn, hlevel⟩ := RetainedCoreObservationTower.hasExtinctionLevel_empty P g
  obtain ⟨t, ht⟩ := ObservedHistory.exists_restrict_isExtinctAtHorizon_of_isExtinctAtHorizon
    (H := ((RetainedCoreObservationTower.empty P g).history n).toHistory) hlevel
  exact ⟨(RetainedCoreObservationTower.empty P g).history n,
    (RetainedCoreObservationTower.empty P g).initial n, t,
    (fun i => Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) i)),
    (fun i => Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) i)),
    ht⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
