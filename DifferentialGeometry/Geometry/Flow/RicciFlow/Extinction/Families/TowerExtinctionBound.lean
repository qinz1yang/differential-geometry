import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerWidthExtinction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreUniformRecords

set_option autoImplicit false

noncomputable section

open scoped Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

namespace ObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

def ExtinctBy (T : ObservationTower P g) (B : ℝ) : Prop :=
  ∃ (b : ℝ) (hb : 0 < b), b ≤ B ∧
    IsEmpty ((T.observe b hb.le).stage
      (Fin.last (T.observe b hb.le).eventCount)).Carrier

def ExtinctAbove (T : ObservationTower P g) (B : ℝ) : Prop :=
  ∀ (b : ℝ) (hb : 0 < b), B < b →
    IsEmpty ((T.observe b hb.le).stage
      (Fin.last (T.observe b hb.le).eventCount)).Carrier

theorem extinctBy_mono (T : ObservationTower P g) {B B' : ℝ} (hBB' : B ≤ B')
    (h : T.ExtinctBy B) : T.ExtinctBy B' := by
  obtain ⟨b, hb, hbB, hempty⟩ := h
  exact ⟨b, hb, hbB.trans hBB', hempty⟩

theorem extinctAbove_of_extinctBy (T : ObservationTower P g) {B : ℝ}
    (h : T.ExtinctBy B) : T.ExtinctAbove B := by
  obtain ⟨b, hb, hbB, hempty⟩ := h
  intro b' hb' hBb'
  exact @ObservationTower.empty_absorbing P g T b b' hb.le hb'.le (hbB.trans hBb'.le) hempty

theorem extinctAbove_mono (T : ObservationTower P g) {B B' : ℝ} (hBB' : B ≤ B')
    (h : T.ExtinctAbove B) : T.ExtinctAbove B' :=
  fun b hb hlt => h b hb (hBB'.trans_lt hlt)

theorem towerExtinct_of_extinctBy (T : ObservationTower P g) {B : ℝ}
    (h : T.ExtinctBy B) : towerExtinct T := by
  obtain ⟨b, hb, _hbB, hempty⟩ := h
  exact ⟨b, hb.le, hempty⟩

theorem towerExtinct_of_extinctAbove (T : ObservationTower P g) {B : ℝ}
    (h : T.ExtinctAbove B) : towerExtinct T := by
  let b := max 1 (B + 1)
  have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_left 1 (B + 1))
  exact ⟨b, hb.le, h b hb (lt_of_lt_of_le (lt_add_one B) (le_max_right 1 (B + 1)))⟩

theorem extinctBy_of_extinctAbove (T : ObservationTower P g) {B : ℝ}
    (h : T.ExtinctAbove B) : T.ExtinctBy (max 1 (B + 1)) := by
  let b := max 1 (B + 1)
  have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_left 1 (B + 1))
  exact ⟨b, hb, le_rfl,
    h b hb (lt_of_lt_of_le (lt_add_one B) (le_max_right 1 (B + 1)))⟩

theorem exists_extinctBy_iff_towerExtinct (T : ObservationTower P g) :
    (∃ B : ℝ, T.ExtinctBy B) ↔ towerExtinct T := by
  constructor
  · rintro ⟨B, hB⟩
    exact T.towerExtinct_of_extinctBy hB
  · intro h
    obtain ⟨B, hB, hbnd⟩ := (towerExtinct_iff_exists_eventually_extinct T).mp h
    exact ⟨B, ⟨B, hB, le_rfl, hbnd B hB.le le_rfl⟩⟩

theorem extinctAbove_iff_towerExtinct (T : ObservationTower P g) :
    (∃ B : ℝ, T.ExtinctAbove B) ↔ towerExtinct T := by
  constructor
  · rintro ⟨B, hB⟩
    exact T.towerExtinct_of_extinctAbove hB
  · intro h
    obtain ⟨B, hB, hbnd⟩ := (towerExtinct_iff_exists_eventually_extinct T).mp h
    exact ⟨B, fun b hbb hBb => hbnd b hbb.le hBb.le⟩

theorem extinctAbove_extinctionThreshold_of_uniformRecordsAbove (T : ObservationTower P g)
    {c A : ℝ} (h : T.UniformRecordsAbove c A) :
    T.ExtinctAbove (extinctionThreshold c A) :=
  T.uniformRecordsAbove_iff_isEmpty_above_threshold.mp h

theorem extinctBy_extinctionThreshold_of_uniformRecordsAbove (T : ObservationTower P g)
    {c A : ℝ} (h : T.UniformRecordsAbove c A) :
    T.ExtinctBy (max 1 (extinctionThreshold c A + 1)) :=
  T.extinctBy_of_extinctAbove (T.extinctAbove_extinctionThreshold_of_uniformRecordsAbove h)

theorem uniformRecordsAbove_of_extinctAbove_extinctionThreshold (T : ObservationTower P g)
    {c A : ℝ} (h : T.ExtinctAbove (extinctionThreshold c A)) :
    T.UniformRecordsAbove c A :=
  T.uniformRecordsAbove_iff_isEmpty_above_threshold.mpr h

theorem extinctAbove_extinctionThreshold_iff_uniformRecordsAbove (T : ObservationTower P g)
    {c A : ℝ} :
    T.ExtinctAbove (extinctionThreshold c A) ↔ T.UniformRecordsAbove c A :=
  T.uniformRecordsAbove_iff_isEmpty_above_threshold.symm

theorem uniformRecordsAbove_mono (T : ObservationTower P g) {c A A' : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (hAA' : A ≤ A') (h : T.UniformRecordsAbove c A) :
    T.UniformRecordsAbove c A' := by
  intro b hb hlt terminal
  have hle : extinctionThreshold c A ≤ extinctionThreshold c A' :=
    (extinctionThreshold_strictMonoOn hc).monotoneOn hA (hA.trans hAA') hAA'
  obtain ⟨R⟩ := h b hb (hle.trans_lt hlt) terminal
  refine ⟨?_⟩
  exact { value := R.value, hypotheses := R.hypotheses, initial_le := R.initial_le.trans hAA' }

theorem extinctAbove_empty (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier]
    (g : P.Metric) (B : ℝ) :
    (RetainedCoreObservationTower.empty P g).toObservationTower.ExtinctAbove B := by
  intro b hb _
  change IsEmpty P.Carrier
  exact hP

theorem extinctBy_empty (P : OrientedThreeStage.{u}) [hP : IsEmpty P.Carrier]
    (g : P.Metric) {B : ℝ} (hB : 0 < B) :
    (RetainedCoreObservationTower.empty P g).toObservationTower.ExtinctBy B := by
  refine ⟨B, hB, le_rfl, ?_⟩
  change IsEmpty P.Carrier
  exact hP

end ObservationTower

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_extinctBy
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {B : ℝ} (hB : T.toObservationTower.ExtinctBy B) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_retainedCoreTower_cutCap M g T hbfr hctrl
    (T.toObservationTower.towerExtinct_of_extinctBy hB)

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_extinctAbove
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {B : ℝ} (hB : T.toObservationTower.ExtinctAbove B) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_retainedCoreTower_extinctBy M g T hbfr hctrl
    (T.toObservationTower.extinctBy_of_extinctAbove hB)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
