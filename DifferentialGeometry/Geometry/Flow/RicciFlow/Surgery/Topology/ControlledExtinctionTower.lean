import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerExtinction

noncomputable section

open Bundle Manifold
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

def hasExtinctObservationTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) : Prop :=
  ∃ T : ObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g,
    (∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      Nonempty (SmoothCutCapCompletion ((T.observe b hb).event i).transition)) ∧
    (∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      letI : ChartedSpace (EuclideanHalfSpace 3) ((T.observe b hb).event i).old :=
        ((T.observe b hb).event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : ((T.observe b hb).event i).old =>
          ((T.observe b hb).event i).transition.trace.capping.coreInclusion x.1)) ∧
    (∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier) ∧
    towerExtinct T

theorem exists_poincare_controlled_extinction_of_extinctObservationTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : hasExtinctObservationTower M g) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) := by
  obtain ⟨T, hc, hout, hctrl, hextinct⟩ := h
  exact exists_poincare_controlled_extinction_of_closedOriented_tower_extinct
    M g T (fun b hb i => (hc b hb i).some) hout hctrl hextinct

theorem not_isEmpty_terminal_at_zero {P : OrientedThreeStage.{u}} {g : P.Metric}
    [Nonempty P.Carrier] (T : ObservationTower P g) :
    ¬ IsEmpty ((T.observe 0 le_rfl).stage (Fin.last (T.observe 0 le_rfl).eventCount)).Carrier := by
  intro h
  have hcount : (T.observe 0 le_rfl).eventCount = 0 :=
    ObservedHistory.eventCount_eq_zero_of_horizon_zero (T.observe 0 le_rfl) rfl
  have hlast : Fin.last (T.observe 0 le_rfl).eventCount =
      (0 : Fin ((T.observe 0 le_rfl).eventCount + 1)) := Fin.ext (by simp [hcount])
  have hne : Nonempty ((T.observe 0 le_rfl).stage
      (Fin.last (T.observe 0 le_rfl).eventCount)).Carrier := by
    have h0 : Nonempty ((T.observe 0 le_rfl).stage 0).Carrier :=
      (T.observeInitial 0 le_rfl).initial_nonempty
    rwa [hlast]
  exact hne.elim fun x => h.false x

theorem towerExtinct_iff_exists_pos {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) [Nonempty P.Carrier] :
    towerExtinct T ↔
      ∃ (b : ℝ) (hb : 0 < b),
        IsEmpty ((T.observe b hb.le).stage
          (Fin.last (T.observe b hb.le).eventCount)).Carrier := by
  constructor
  · rintro ⟨b, hb, h⟩
    rcases eq_or_lt_of_le hb with h0 | hpos
    · subst h0
      exact absurd (by simpa using h) (not_isEmpty_terminal_at_zero T)
    · exact ⟨b, hpos, h⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb.le, h⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery
