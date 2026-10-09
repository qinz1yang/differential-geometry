import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Geometrization.OrientedReconstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.RawSurgery
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionAssembly

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

structure HistoryEndpointInputs (H : ObservedHistory.{u}) where
  completion : (i : Fin H.eventCount) → SmoothCutCapCompletion (H.event i).transition
  reconstruction : (i : Fin H.eventCount) → OrientedEventReconstruction
    (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphericalCutCapTransition.ofSmoothCutCapTransition
      (H.event i).transition (completion i))
  discarded : ∀ i : Fin H.eventCount,
    ComponentsGeometrize (H.event i).discarded.toClosedOrientedManifold
  cycles : ∀ (i : Fin H.eventCount) (w : (reconstruction i).data.Group),
    0 < (reconstruction i).data.sphereProducts w →
      Geometrizes (sphereTwoTimesCircleLift.ulift.{0, u})

namespace HistoryEndpointInputs
variable {H : ObservedHistory.{u}}

theorem stages (K : HistoryEndpointInputs H)
    (final : ComponentsGeometrize (H.stage (Fin.last H.eventCount)).toClosedOrientedManifold)
    (j : Fin (H.eventCount + 1)) :
    ComponentsGeometrize (H.stage j).toClosedOrientedManifold := by
  induction j using Fin.reverseInduction with
  | last => exact final
  | cast i ih =>
    exact (K.reconstruction i).componentsGeometrize ih (K.discarded i) (K.cycles i)

def initialOrientedDiffeomorph {P : OrientedThreeStage.{u}} {g : P.Metric}
    (A : InitialIdentification P g H) :
    ClosedOrientedManifold.OrientedDiffeomorph P.toClosedOrientedManifold
      (H.stage 0).toClosedOrientedManifold :=
  ⟨A.map, OrientedThreeStage.preservesOrientation_toClosedOrientedManifold A.positive⟩

theorem initial_map {P : OrientedThreeStage.{u}} {g : P.Metric}
    (A : InitialIdentification P g H) :
    (initialOrientedDiffeomorph A).val = A.map := rfl

theorem initial {P : OrientedThreeStage.{u}} {g : P.Metric}
    (K : HistoryEndpointInputs H) (A : InitialIdentification P g H)
    (final : ComponentsGeometrize (H.stage (Fin.last H.eventCount)).toClosedOrientedManifold) :
    ComponentsGeometrize P.toClosedOrientedManifold :=
  componentsGeometrize_of_orientedDiffeomorph (initialOrientedDiffeomorph A)
    (K.stages final 0)

theorem geometrizes (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (K : HistoryEndpointInputs H)
    (A : InitialIdentification
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H)
    (final : ComponentsGeometrize (H.stage (Fin.last H.eventCount)).toClosedOrientedManifold) :
    Geometrizes M := by
  apply (componentsGeometrize_iff M).mp
  simpa only [OrientedThreeStage.ofClosedOrientedManifold_toClosedOrientedManifold]
    using K.initial A final

theorem terminal (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (K : HistoryEndpointInputs H)
    (A : InitialIdentification
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H)
    (empty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier) : Geometrizes M := by
  let : IsEmpty (H.stage (Fin.last H.eventCount)).toClosedOrientedManifold.Carrier := empty
  exact K.geometrizes M A (componentsGeometrize_of_isEmpty _)

def atZero (P : OrientedThreeStage.{u}) (g : P.Metric) :
    HistoryEndpointInputs (ObservedHistory.atZero P g) where
  completion i := Fin.elim0 i
  reconstruction i := Fin.elim0 i
  discarded i := Fin.elim0 i
  cycles i := Fin.elim0 i

end HistoryEndpointInputs

def ObservedTopologySupply {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) : Prop :=
  ∀ (b : ℝ) (hb : 0 ≤ b), Nonempty (HistoryEndpointInputs (T.observe b hb))

def LateComponentSupply {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) : Prop :=
  ∃ B : ℝ, ∀ (t : ℝ) (ht : 0 < t), B < t → t ∉ T.eventTimes →
    (T.observe t ht.le).time (Fin.last (T.observe t ht.le).eventCount) < t →
    Nonempty ((T.observe t ht.le).stage (Fin.last (T.observe t ht.le).eventCount)).Carrier →
    ComponentsGeometrize
      ((T.observe t ht.le).stage (Fin.last (T.observe t ht.le).eventCount)).toClosedOrientedManifold

theorem geometrizes_of_observation_supplies
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (T : ObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (topology : ObservedTopologySupply T) (late : LateComponentSupply T) :
    Geometrizes M := by
  rcases GC.Surgery.marked_late_or_empty_prefixes T with
    ⟨a, ha, A, _, hempty, _⟩ | hlate
  · obtain ⟨K⟩ := topology a ha
    exact K.terminal M A (hempty a ha le_rfl)
  · obtain ⟨B, hB⟩ := late
    obtain ⟨t, ht, A, hBt, hregular, hslab, _, hnonempty⟩ := hlate B
    obtain ⟨K⟩ := topology t ht.le
    exact K.geometrizes M A (hB t ht hBt hregular hslab hnonempty)

theorem geometrizes_of_rawSurgery_supplies
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {g : (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Metric}
    (F : GC.Interface.RawSurgery
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (topology : ObservedTopologySupply F.observation)
    (late : LateComponentSupply F.observation) : Geometrizes M :=
  geometrizes_of_observation_supplies M F.observation topology late

end GC.Endpoint
