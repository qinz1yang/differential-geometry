import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ScalarThreshold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinctionLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerWidthExtinction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CoreCompatibleExtinctionTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EmbeddedCoreExtinctionTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctObservationNucleus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreExtinctionLevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_hasExtinctObservationNucleusWithCompletion
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h : HasExtinctObservationNucleusWithCompletion P g) :
    HasExtinctObservationNucleusOfCutCapCompletion P g :=
  hasExtinctObservationNucleusOfCutCapCompletion_of_nucleus P g
    ((hasExtinctObservationNucleusWithCompletion_iff P g).mp h)

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_hasExtinctStandardSideNucleus
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (h : HasExtinctStandardSideNucleus P g) :
    HasExtinctObservationNucleusOfCutCapCompletion P g :=
  hasExtinctObservationNucleusOfCutCapCompletion_of_nucleus P g
    (hasExtinctStandardSideNucleus_implies P g h)

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_hasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistory M g) :
    HasExtinctObservationNucleusOfCutCapCompletion
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g :=
  hasExtinctObservationNucleusOfCutCapCompletion_of_nucleus
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g
    (hasExtinctObservationNucleus_of_hasExtinctRetainedCoreHistory M g h)

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_hasExtinctRetainedCoreHistoryAtTime
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistoryAtTime M g) :
    HasExtinctObservationNucleusOfCutCapCompletion
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g :=
  hasExtinctObservationNucleusOfCutCapCompletion_of_hasExtinctRetainedCoreHistory M g
    (hasExtinctRetainedCoreHistory_of_hasExtinctRetainedCoreHistoryAtTime M g h)

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_hasExtinctRetainedCoreTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreTower M g) :
    HasExtinctObservationNucleusOfCutCapCompletion
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g :=
  hasExtinctObservationNucleusOfCutCapCompletion_of_hasExtinctRetainedCoreHistory M g
    (hasExtinctRetainedCoreHistory_of_hasExtinctRetainedCoreTower M g h)

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_hasExtinctObservationTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower M g) :
    HasExtinctObservationNucleusOfCutCapCompletion
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g := by
  obtain ⟨T, hc, hout, hctrl, hextinct⟩ := h
  obtain ⟨b, hb, hempty⟩ := hextinct
  exact ⟨T.observe b hb, T.observeInitial b hb, fun i => hc b hb i,
    fun i => hout b hb i, fun i => hctrl b hb i, hempty⟩

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_hasCoreCompatibleObservationTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower M g) :
    HasExtinctObservationNucleusOfCutCapCompletion
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g :=
  hasExtinctObservationNucleusOfCutCapCompletion_of_hasExtinctObservationTower M g
    (DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_coreCompatible
      M g h)

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_hasEmbeddedCoreObservationTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : hasEmbeddedCoreObservationTower M g) :
    HasExtinctObservationNucleusOfCutCapCompletion
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g :=
  hasExtinctObservationNucleusOfCutCapCompletion_of_hasExtinctObservationTower M g
    (hasExtinctObservationTower_of_embeddedCore M g h)

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_retainedCoreTower_extinctByLevelWithin
    (P : OrientedThreeStage.{u}) (g : P.Metric) (T : RetainedCoreObservationTower P g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {B : ℝ} (hB : T.toObservationTower.ExtinctByLevelWithin B) :
    HasExtinctObservationNucleusOfCutCapCompletion P g :=
  hasExtinctObservationNucleusOfCutCapCompletion_of_tower_extinctBy P g T hbfr hctrl
    (T.toObservationTower.extinctBy_of_extinctByLevelWithin hB)

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_retainedCoreTower_extinct
    (P : OrientedThreeStage.{u}) (g : P.Metric) (T : RetainedCoreObservationTower P g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    (h : towerExtinct T.toObservationTower) :
    HasExtinctObservationNucleusOfCutCapCompletion P g := by
  obtain ⟨B, hB⟩ := (T.toObservationTower.exists_extinctBy_iff_towerExtinct).mpr h
  exact hasExtinctObservationNucleusOfCutCapCompletion_of_tower_extinctBy P g T hbfr hctrl hB

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_retainedCoreTower_uniformRecordsAbove
    (P : OrientedThreeStage.{u}) (g : P.Metric) (T : RetainedCoreObservationTower P g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {c A : ℝ} (h : T.toObservationTower.UniformRecordsAbove c A) :
    HasExtinctObservationNucleusOfCutCapCompletion P g := by
  obtain ⟨B, hB⟩ := (T.hasExtinctionLevel_iff_exists_extinctByLevelWithin).mp
    (T.hasExtinctionLevel_of_uniformRecordsAbove h)
  exact hasExtinctObservationNucleusOfCutCapCompletion_of_retainedCoreTower_extinctByLevelWithin
    P g T hbfr hctrl hB

theorem exists_extinctionThreshold_ge (B : ℝ) :
    ∃ c A : ℝ, 0 < c ∧ 0 ≤ A ∧ B ≤ extinctionThreshold c A := by
  by_cases hB : B ≤ 0
  · exact ⟨1, 0, one_pos, le_rfl,
      by rw [(extinctionThreshold_eq_zero_iff one_pos le_rfl).mpr rfl]; exact hB⟩
  · have hBpos : 0 < B := not_le.mp hB
    have hA : 0 ≤ 8 * Real.pi * ((B + 1) ^ (1 / 4 : ℝ) - 1) := by
      have hr : 1 < (B + 1) ^ (1 / 4 : ℝ) :=
        Real.one_lt_rpow (by linarith) (by norm_num)
      have hp := Real.pi_pos
      nlinarith
    refine ⟨1, 8 * Real.pi * ((B + 1) ^ (1 / 4 : ℝ) - 1), one_pos, hA, ?_⟩
    refine not_lt.mp fun hlt => ?_
    rw [extinctionThreshold_lt_iff one_pos hA hBpos.le] at hlt
    have hzero : 8 * Real.pi * ((B + 1) ^ (1 / 4 : ℝ) - 1) / (1 : ℝ) ^ (3 / 4 : ℝ) -
        8 * Real.pi * ((B + 1) ^ (1 / 4 : ℝ) - (1 : ℝ) ^ (1 / 4 : ℝ)) = 0 := by
      rw [Real.one_rpow, Real.one_rpow, div_one, sub_self]
    rw [hzero] at hlt
    exact lt_irrefl 0 hlt

theorem exists_uniformRecordsAbove_of_hasExtinctionLevel {P : OrientedThreeStage.{u}}
    {g : P.Metric} (T : RetainedCoreObservationTower P g) (h : T.HasExtinctionLevel) :
    ∃ c A : ℝ, T.toObservationTower.UniformRecordsAbove c A := by
  obtain ⟨n, _hn, hext⟩ := h
  obtain ⟨c, A, _hc, _hA, hnA⟩ := exists_extinctionThreshold_ge (n : ℝ)
  refine ⟨c, A, ?_⟩
  exact T.toObservationTower.uniformRecordsAbove_of_extinctAbove_extinctionThreshold
    (T.toObservationTower.extinctAbove_of_history_isExtinctAtHorizon hnA hext)

theorem exists_retainedCoreTower_extinctByLevelWithin_iff_hasExtinctRetainedCoreTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    (∃ T : RetainedCoreObservationTower
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g,
      T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧
        ∃ B : ℝ, T.toObservationTower.ExtinctByLevelWithin B) ↔
      HasExtinctRetainedCoreTower M g := by
  constructor
  · rintro ⟨T, hbfr, hctrl, B, hB⟩
    exact ⟨T, hbfr, hctrl,
      (T.hasExtinctionLevel_iff_exists_extinctByLevelWithin).mpr ⟨B, hB⟩⟩
  · rintro ⟨T, hbfr, hctrl, hlevel⟩
    exact ⟨T, hbfr, hctrl,
      (T.hasExtinctionLevel_iff_exists_extinctByLevelWithin).mp hlevel⟩

theorem exists_retainedCoreTower_uniformRecordsAbove_iff_hasExtinctRetainedCoreTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    (∃ T : RetainedCoreObservationTower
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g,
      T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧
        ∃ c A : ℝ, T.toObservationTower.UniformRecordsAbove c A) ↔
      HasExtinctRetainedCoreTower M g := by
  constructor
  · rintro ⟨T, hbfr, hctrl, c, A, hrec⟩
    exact ⟨T, hbfr, hctrl, T.hasExtinctionLevel_of_uniformRecordsAbove hrec⟩
  · rintro ⟨T, hbfr, hctrl, hlevel⟩
    obtain ⟨c, A, hrec⟩ := exists_uniformRecordsAbove_of_hasExtinctionLevel T hlevel
    exact ⟨T, hbfr, hctrl, c, A, hrec⟩

theorem hasExtinctStandardSideNucleus_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) : HasExtinctStandardSideNucleus P g := by
  refine ⟨ObservedHistory.atZero P g, InitialIdentification.reflAtZero P g, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · exact hP

theorem hasExtinctObservationNucleusWithCompletion_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) :
    HasExtinctObservationNucleusWithCompletion P g :=
  (hasExtinctObservationNucleusWithCompletion_iff P g).mpr
    (hasExtinctObservationNucleus_of_isEmpty P g)

theorem hasExtinctObservationNucleusOfCutCapCompletion_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) :
    HasExtinctObservationNucleusOfCutCapCompletion P g :=
  hasExtinctObservationNucleusOfCutCapCompletion_of_nucleus P g
    (hasExtinctObservationNucleus_of_isEmpty P g)

theorem exists_retainedCoreTower_extinctByLevelWithin_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) :
    ∃ T : RetainedCoreObservationTower P g,
      T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧
        ∃ B : ℝ, T.toObservationTower.ExtinctByLevelWithin B := by
  refine ⟨RetainedCoreObservationTower.empty P g, ?_, ?_, ?_⟩
  · intro n j
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)
  · intro n j
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)
  · exact (RetainedCoreObservationTower.hasExtinctionLevel_iff_exists_extinctByLevelWithin
      (RetainedCoreObservationTower.empty P g)).mp
      (RetainedCoreObservationTower.hasExtinctionLevel_empty P g)

theorem exists_retainedCoreTower_uniformRecordsAbove_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) :
    ∃ T : RetainedCoreObservationTower P g,
      T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧
        ∃ c A : ℝ, T.toObservationTower.UniformRecordsAbove c A := by
  refine ⟨RetainedCoreObservationTower.empty P g, ?_, ?_, ?_⟩
  · intro n j
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)
  · intro n j
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)
  · exact exists_uniformRecordsAbove_of_hasExtinctionLevel
      (RetainedCoreObservationTower.empty P g)
      (RetainedCoreObservationTower.hasExtinctionLevel_empty P g)

theorem HasExtinctObservationNucleusOfCutCapCompletion.exists_eventCount_pos
    {P : OrientedThreeStage.{u}} {g : P.Metric} [Nonempty P.Carrier]
    (h : HasExtinctObservationNucleusOfCutCapCompletion P g) :
    ∃ (H : ObservedHistory.{u}) (_ : InitialIdentification P g H), 0 < H.eventCount := by
  obtain ⟨H, A, _, _, _, hempty⟩ := h
  exact ⟨H, A, @ObservedHistory.eventCount_pos_of_final_empty H A.initial_nonempty hempty⟩

theorem isEmpty_carrier_frontier_collapse (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier]
    (g : P.Metric) :
    HasExtinctObservationNucleus P g ∧ HasExtinctObservationNucleusWithCompletion P g ∧
      HasExtinctStandardSideNucleus P g ∧ HasExtinctObservationNucleusOfCutCapCompletion P g ∧
      (∃ T : RetainedCoreObservationTower P g,
        T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧ T.HasExtinctionLevel) ∧
      (∃ T : RetainedCoreObservationTower P g,
        T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧
          ∃ c A : ℝ, T.toObservationTower.UniformRecordsAbove c A) ∧
      (RetainedCoreObservationTower.empty P g).toObservationTower.ExtinctByLevelWithin 1 ∧
      ((RetainedCoreObservationTower.empty P g).toObservationTower.ExtinctBy (1 / 2) ∧
        ¬ (RetainedCoreObservationTower.empty P g).toObservationTower.ExtinctByLevelWithin
          (1 / 2)) := by
  refine ⟨hasExtinctObservationNucleus_of_isEmpty P g,
    hasExtinctObservationNucleusWithCompletion_of_isEmpty P g,
    hasExtinctStandardSideNucleus_of_isEmpty P g,
    hasExtinctObservationNucleusOfCutCapCompletion_of_isEmpty P g, ?_, ?_,
    ObservationTower.extinctByLevelWithin_empty P g le_rfl,
    ObservationTower.extinctBy_half_empty_not_extinctByLevelWithin P g⟩
  · exact ⟨RetainedCoreObservationTower.empty P g, (fun n j => Fin.elim0 (Fin.cast
      (RetainedCoreObservationTower.empty_eventCount P g n) j)),
      (fun n j => Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)),
      RetainedCoreObservationTower.hasExtinctionLevel_empty P g⟩
  · exact exists_retainedCoreTower_uniformRecordsAbove_of_isEmpty P g

theorem not_exists_isEmpty_carrier_connectedClosedOrientedManifold :
    ¬ ∃ M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3,
      IsEmpty M.Carrier := by
  rintro ⟨M, hM⟩
  exact not_isEmpty_carrier_of_connectedClosedOrientedManifold M hM

theorem exists_extinctBy_not_extinctByLevelWithin (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) :
    ∃ T : ObservationTower P g, T.ExtinctBy (1 / 2) ∧ ¬ T.ExtinctByLevelWithin (1 / 2) :=
  ⟨(RetainedCoreObservationTower.empty P g).toObservationTower,
    (ObservationTower.extinctBy_half_empty_not_extinctByLevelWithin P g).1,
    (ObservationTower.extinctBy_half_empty_not_extinctByLevelWithin P g).2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
