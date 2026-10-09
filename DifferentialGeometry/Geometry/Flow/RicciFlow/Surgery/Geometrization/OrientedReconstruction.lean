import DifferentialGeometry.Topology.ThreeManifold.Geometrization.FiniteConnectedSum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MarkedReconstruction
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.Endpoint
universe u

def ComponentsGeometrize (M : ClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents M.Carrier, Geometrizes (M.component C)

theorem componentsGeometrize_of_orientedDiffeomorph
    {M N : ClosedOrientedManifold.{u} 3}
    (f : ClosedOrientedManifold.OrientedDiffeomorph M N)
    (h : ComponentsGeometrize N) : ComponentsGeometrize M := by
  intro C
  exact geometrizes_of_orientedDiffeomorph (f.component C).symm (h _)

theorem componentsGeometrize_iff (M : ConnectedClosedOrientedManifold.{u} 3) :
    ComponentsGeometrize M.toClosedOrientedManifold ↔ Geometrizes M := by
  constructor
  · intro h
    let C := ConnectedComponents.mk (Classical.choice (inferInstance : Nonempty M.Carrier))
    exact geometrizes_of_orientedDiffeomorph
      (M.toClosedOrientedManifold.componentOrientedDiffeomorph C) (h C)
  · intro h C
    exact geometrizes_of_orientedDiffeomorph
      (M.toClosedOrientedManifold.componentOrientedDiffeomorph C).symm h

theorem componentsGeometrize_of_isEmpty (M : ClosedOrientedManifold.{u} 3)
    [IsEmpty M.Carrier] : ComponentsGeometrize M := by
  intro C
  obtain ⟨x, _⟩ := ConnectedComponents.surjective_coe C
  exact isEmptyElim x

structure OrientedEventReconstruction {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) where
  data : GC.Surgery.CutCapSumData E
  sourceComponent : data.Group ≃ ConnectedComponents M.Carrier
  comparison : (w : data.Group) → ClosedOrientedManifold.OrientedDiffeomorph
    (finiteConnectedSum ((data.factors w).map E.capped.component ++
      List.replicate (data.sphereProducts w)
        (sphereTwoTimesCircleLift.ulift.{0, u}))).toClosedOrientedManifold
    (M.component (sourceComponent w)).toClosedOrientedManifold
  map_eq : ∀ w x, data.reconstruct ((comparison w).val x).val = ⟨w, x⟩

namespace OrientedEventReconstruction
variable {M Q : ClosedOrientedManifold.{u} 3} {E : SphericalCutCapTransition M Q}

theorem target_slot_bijective (R : OrientedEventReconstruction E) :
    Function.Bijective (GC.Surgery.presentationComponentEquiv E ∘
      GC.Surgery.componentSlot R.data) :=
  GC.Surgery.actual_target_slot_bijective R.data

theorem componentsGeometrize (R : OrientedEventReconstruction E)
    (retained : ComponentsGeometrize Q)
    (discarded : ComponentsGeometrize E.discarded)
    (cycles : ∀ w, 0 < R.data.sphereProducts w →
      Geometrizes (sphereTwoTimesCircleLift.ulift.{0, u})) :
    ComponentsGeometrize M := by
  have capped : ComponentsGeometrize E.capped := by
    intro K
    rcases GC.Surgery.cap_component_retained_or_discarded E K with
      ⟨q, _, ⟨f⟩⟩ | ⟨d, _, ⟨f⟩⟩
    · exact geometrizes_of_orientedDiffeomorph f.symm (retained _)
    · exact geometrizes_of_orientedDiffeomorph f.symm (discarded _)
  intro C
  obtain ⟨w, rfl⟩ := R.sourceComponent.surjective C
  apply geometrizes_of_markedFactors _ _ _ ⟨R.comparison w⟩
  intro P hP
  rcases List.mem_append.mp hP with hP | hP
  · obtain ⟨K, _, rfl⟩ := List.mem_map.mp hP
    exact capped K
  · obtain ⟨hn, rfl⟩ := List.mem_replicate.mp hP
    exact cycles w (Nat.pos_of_ne_zero hn)

end OrientedEventReconstruction
end GC.Endpoint
