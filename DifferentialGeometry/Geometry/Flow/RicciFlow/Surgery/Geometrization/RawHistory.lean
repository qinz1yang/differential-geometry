import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.SmoothReconstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.ObservedHistory

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.Interface
namespace GC.Endpoint
universe u

theorem componentsGeometrize_history (H : ObservedHistory.{u})
    (completion : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (discarded : ∀ i : Fin H.eventCount,
      ComponentsGeometrize (H.event i).discarded.toClosedOrientedManifold)
    (cycles : ∀ _i : Fin H.eventCount, Geometrizes (sphereTwoTimesCircleLift.ulift.{0, u}))
    (final : ComponentsGeometrize (H.stage (Fin.last H.eventCount)).toClosedOrientedManifold)
    (j : Fin (H.eventCount + 1)) :
    ComponentsGeometrize (H.stage j).toClosedOrientedManifold := by
  induction j using Fin.reverseInduction with
  | last => exact final
  | cast i ih =>
    exact componentsGeometrize_of_cutCap
      (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphericalCutCapTransition.ofSmoothCutCapTransition
        (H.event i).transition (completion i)) ih (discarded i) (cycles i)

theorem geometrizes_of_smooth_history (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (H : ObservedHistory.{u})
    (A : InitialIdentification
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H)
    (completion : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition)
    (discarded : ∀ i : Fin H.eventCount,
      ComponentsGeometrize (H.event i).discarded.toClosedOrientedManifold)
    (cycles : ∀ _i : Fin H.eventCount, Geometrizes (sphereTwoTimesCircleLift.ulift.{0, u}))
    (final : ComponentsGeometrize (H.stage (Fin.last H.eventCount)).toClosedOrientedManifold) :
    Geometrizes M := by
  have h0 := componentsGeometrize_history H completion discarded cycles final 0
  have hM := componentsGeometrize_of_orientedDiffeomorph
    (HistoryEndpointInputs.initialOrientedDiffeomorph A) h0
  apply (componentsGeometrize_iff M).mp
  simpa only [OrientedThreeStage.ofClosedOrientedManifold_toClosedOrientedManifold] using hM

theorem geometrizes_of_raw_observation
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (F : RawSurgery
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (standard : StandardFactorEndpoints.{u}) (b : ℝ) (hb : 0 ≤ b)
    (final : ComponentsGeometrize
      ((F.observation.observe b hb).stage
        (Fin.last (F.observation.observe b hb).eventCount)).toClosedOrientedManifold) :
    Geometrizes M := by
  have hcompletion := F.tower.hasCutCapCompletion_toObservationTower
    (fun n i => (F.event_control n i).2.1) b hb
  have hdiscard := F.tower.poincareStandardDiscarded_toObservationTower
    (fun n i => (F.event_control n i).2.2) b hb
  exact geometrizes_of_smooth_history M (F.observation.observe b hb) (F.initial b hb)
    (fun i => (hcompletion i).some)
    (fun i C => geometrizes_of_poincareStandard standard _ (hdiscard i C))
    (fun _ => cycle_geometrizes_of_standard standard) final

theorem geometrizes_of_raw_terminal
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (F : RawSurgery
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (standard : StandardFactorEndpoints.{u}) (b : ℝ) (hb : 0 ≤ b)
    (empty : IsEmpty ((F.observation.observe b hb).stage
      (Fin.last (F.observation.observe b hb).eventCount)).Carrier) : Geometrizes M := by
  let : IsEmpty ((F.observation.observe b hb).stage
    (Fin.last (F.observation.observe b hb).eventCount)).toClosedOrientedManifold.Carrier := empty
  exact geometrizes_of_raw_observation M F standard b hb (componentsGeometrize_of_isEmpty _)

theorem geometrizes_of_raw_standard_late
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (F : RawSurgery
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (standard : StandardFactorEndpoints.{u}) (late : LateComponentSupply F.observation) :
    Geometrizes M := by
  rcases GC.Surgery.marked_late_or_empty_prefixes F.observation with
    ⟨a, ha, _, _, hempty, _⟩ | hlate
  · exact geometrizes_of_raw_terminal M F standard a ha (hempty a ha le_rfl)
  · obtain ⟨B, hB⟩ := late
    obtain ⟨t, ht, _, hBt, hregular, hslab, _, hnonempty⟩ := hlate B
    exact geometrizes_of_raw_observation M F standard t ht.le
      (hB t ht hBt hregular hslab hnonempty)

end GC.Endpoint
