import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparisonRecord
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ObservationTower

noncomputable section

open Set Filter
open Bundle Manifold
open scoped Topology ENNReal Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

def towerExtinct {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) : Prop :=
  ∃ (b : ℝ) (hb : 0 ≤ b),
    IsEmpty ((T.observe b hb).stage (Fin.last (T.observe b hb).eventCount)).Carrier

namespace ObservedHistory

theorem not_uniform_records_of_horizon_eq_zero (H : ObservedHistory.{u}) {c A : ℝ}
    (hh : H.horizon = 0)
    (hne : Nonempty (H.stage (Fin.last H.eventCount)).Carrier) :
    ¬ (∀ _Q : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier,
        Nonempty (ObservedComparisonRecord H c A)) := by
  intro records
  obtain ⟨R⟩ := records (ConnectedComponents.mk hne.some)
  have hpos : 0 < H.horizon := R.hypotheses.horizon_pos
  rw [hh] at hpos
  exact absurd hpos (lt_irrefl 0)

theorem uniform_records_iff_final_empty_of_threshold_lt (H : ObservedHistory.{u}) {c A : ℝ}
    (hH : extinctionThreshold c A < H.horizon) :
    (∀ _Q : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier,
      Nonempty (ObservedComparisonRecord H c A)) ↔
      IsEmpty (H.stage (Fin.last H.eventCount)).Carrier :=
  ⟨fun records => H.final_empty_of_uniform_records hH records,
    fun hempty _Q =>
      False.elim ((ConnectedComponents.isEmpty_iff_isEmpty.mpr hempty).false _Q)⟩

end ObservedHistory

namespace ObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem records_iff_final_empty_of_threshold_lt (T : ObservationTower P g) (b : ℝ) (hb : 0 ≤ b)
    {c A : ℝ} (h : extinctionThreshold c A < b) :
    (∀ _terminal : ConnectedComponents ((T.observe b hb).stage
        (Fin.last (T.observe b hb).eventCount)).Carrier,
      Nonempty (ObservedComparisonRecord (T.observe b hb) c A)) ↔
      IsEmpty ((T.observe b hb).stage (Fin.last (T.observe b hb).eventCount)).Carrier :=
  ObservedHistory.uniform_records_iff_final_empty_of_threshold_lt (T.observe b hb) h

theorem uniform_records_iff_records_below_threshold_and_extinct (T : ObservationTower P g)
    {c A : ℝ} :
    (∀ (b : ℝ) (hb : 0 < b) (_terminal : ConnectedComponents ((T.observe b hb.le).stage
        (Fin.last (T.observe b hb.le).eventCount)).Carrier),
      Nonempty (ObservedComparisonRecord (T.observe b hb.le) c A)) ↔
      ((∀ (b : ℝ) (hb : 0 < b), b ≤ extinctionThreshold c A →
        ∀ _terminal : ConnectedComponents ((T.observe b hb.le).stage
          (Fin.last (T.observe b hb.le).eventCount)).Carrier,
        Nonempty (ObservedComparisonRecord (T.observe b hb.le) c A)) ∧
      (∀ (b : ℝ) (hb : 0 < b), extinctionThreshold c A < b →
        IsEmpty ((T.observe b hb.le).stage
          (Fin.last (T.observe b hb.le).eventCount)).Carrier)) := by
  constructor
  · intro records
    exact ⟨fun b hb _ => records b hb,
      fun b hb hlt => (T.records_iff_final_empty_of_threshold_lt b hb.le hlt).mp (records b hb)⟩
  · rintro ⟨below, above⟩ b hb
    by_cases hle : b ≤ extinctionThreshold c A
    · exact below b hb hle
    · have hlt : extinctionThreshold c A < b := lt_of_not_ge hle
      exact (T.records_iff_final_empty_of_threshold_lt b hb.le hlt).mpr (above b hb hlt)

theorem not_uniform_records_including_zero_horizon (T : ObservationTower P g)
    [Nonempty P.Carrier] {c A : ℝ} :
    ¬ (∀ (b : ℝ) (hb : 0 ≤ b)
      (_terminal : ConnectedComponents ((T.observe b hb).stage
        (Fin.last (T.observe b hb).eventCount)).Carrier),
      Nonempty (ObservedComparisonRecord (T.observe b hb) c A)) := by
  intro records
  have hh : (T.observe 0 le_rfl).horizon = 0 := rfl
  have hcount : (T.observe 0 le_rfl).eventCount = 0 :=
    ObservedHistory.eventCount_eq_zero_of_horizon_zero (T.observe 0 le_rfl) hh
  have hlast : Fin.last (T.observe 0 le_rfl).eventCount =
      (0 : Fin ((T.observe 0 le_rfl).eventCount + 1)) := Fin.ext (by simp [hcount])
  have hne : Nonempty ((T.observe 0 le_rfl).stage
      (Fin.last (T.observe 0 le_rfl).eventCount)).Carrier := by
    have h0 : Nonempty ((T.observe 0 le_rfl).stage 0).Carrier :=
      (T.observeInitial 0 le_rfl).initial_nonempty
    rwa [hlast]
  exact ObservedHistory.not_uniform_records_of_horizon_eq_zero (T.observe 0 le_rfl) hh hne
    (fun Q => records 0 le_rfl Q)

theorem uniform_records_below_threshold_of_isEmpty_at_zero (T : ObservationTower P g) {c A : ℝ}
    (h0 : IsEmpty ((T.observe 0 le_rfl).stage (Fin.last (T.observe 0 le_rfl).eventCount)).Carrier) :
    ∀ (b : ℝ) (hb : 0 < b), b ≤ extinctionThreshold c A →
      ∀ _terminal : ConnectedComponents ((T.observe b hb.le).stage
        (Fin.last (T.observe b hb.le).eventCount)).Carrier,
        Nonempty (ObservedComparisonRecord (T.observe b hb.le) c A) := by
  intro b hb _hle terminal
  have hb0 : 0 ≤ b := hb.le
  have hempty : IsEmpty ((T.observe b hb0).stage
      (Fin.last (T.observe b hb0).eventCount)).Carrier :=
    @ObservationTower.empty_absorbing P g T 0 b le_rfl hb0 hb0 h0
  exact False.elim ((ConnectedComponents.isEmpty_iff_isEmpty.mpr hempty).false terminal)

end ObservationTower

theorem exists_poincare_controlled_extinction_of_tower_extinct {P : OrientedThreeStage.{u}}
    {g : P.Metric} (T : ObservationTower P g) [Nonempty P.Carrier]
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      SmoothCutCapCompletion ((T.observe b hb).event i).transition)
    (hout : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      letI : ChartedSpace (EuclideanHalfSpace 3) ((T.observe b hb).event i).old :=
        ((T.observe b hb).event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : ((T.observe b hb).event i).old =>
          ((T.observe b hb).event i).transition.trace.capping.coreInclusion x.1))
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier)
    (hextinct : towerExtinct T) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  obtain ⟨b, hb, hempty⟩ := hextinct
  exact exists_poincare_controlled_extinction_of_observedHistory P g (T.observe b hb)
    (T.observeInitial b hb) (hc b hb) (hout b hb) (hctrl b hb) hempty

theorem exists_poincare_controlled_extinction_of_closedOriented_tower_extinct
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    [Nonempty M.Carrier] (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : ObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      SmoothCutCapCompletion ((T.observe b hb).event i).transition)
    (hout : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      letI : ChartedSpace (EuclideanHalfSpace 3) ((T.observe b hb).event i).old :=
        ((T.observe b hb).event i).oldCharts
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : ((T.observe b hb).event i).old =>
          ((T.observe b hb).event i).transition.trace.capping.coreInclusion x.1))
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier)
    (hextinct : towerExtinct T) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  @exists_poincare_controlled_extinction_of_tower_extinct
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g T
    ‹Nonempty M.Carrier› hc hout hctrl hextinct

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
