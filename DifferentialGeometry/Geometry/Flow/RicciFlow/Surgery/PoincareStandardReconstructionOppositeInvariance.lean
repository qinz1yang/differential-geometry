import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Poincare
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.PoincareStandardReconstruction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeInvariance

set_option autoImplicit false
noncomputable section

open Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

theorem
    exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction_of_oppositeInvariance
    {M : Topology.ClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (W : PoincareControlledExtinction M g)
    (hunitR : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum X
        Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hunitL : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum Topology.standardThreeSphereLift.{u} X
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hassoc : ∀ X Y Z : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum (Topology.connectedSum X Y) Z
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (Topology.connectedSum X (Topology.connectedSum Y Z)).toClosedOrientedManifold.Carrier))
    (hop : Topology.connectedSumOppositeInvariance.{u})
    (hsum : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).componentConnectedSumDecomposition)
    [ConnectedSpace M.Carrier] [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier) :=
  exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction (W := W)
    (hunitR := hunitR) (hunitL := hunitL) (hassoc := hassoc)
    (htransportL := Topology.connectedSum_transport_left_of_oppositeInvariance hop)
    (htransportR := Topology.connectedSum_transport_right_of_oppositeInvariance hop)
    (hsum := hsum)

theorem smoothPoincareConjecture_of_poincareControlledExtinction_of_oppositeInvariance
    (hunitR : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum X
        Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hunitL : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum Topology.standardThreeSphereLift.{u} X
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hassoc : ∀ X Y Z : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum (Topology.connectedSum X Y) Z
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (Topology.connectedSum X (Topology.connectedSum Y Z)).toClosedOrientedManifold.Carrier))
    (hop : Topology.connectedSumOppositeInvariance.{u})
    (hsum : ∀ (H : FiniteSurgeryHistory.{u}) (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (hext : ∀ (M : Topology.ConnectedClosedOrientedManifold.{u} 3) [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)) :
    smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_poincareControlledExtinction
    (hunitR := hunitR) (hunitL := hunitL) (hassoc := hassoc)
    (htransportL := Topology.connectedSum_transport_left_of_oppositeInvariance hop)
    (htransportR := Topology.connectedSum_transport_right_of_oppositeInvariance hop)
    (hsum := hsum) (hext := hext)

theorem
    exists_diffeomorph_standardThreeSphere_of_standardDecomposition_of_oppositeInvariance
    {M : Topology.ClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (W : PoincareControlledExtinction M g)
    (hunitR : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum X
        Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hunitL : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum Topology.standardThreeSphereLift.{u} X
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hassoc : ∀ X Y Z : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum (Topology.connectedSum X Y) Z
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (Topology.connectedSum X (Topology.connectedSum Y Z)).toClosedOrientedManifold.Carrier))
    (hop : Topology.connectedSumOppositeInvariance.{u})
    (hsum : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).componentConnectedSumStandardDecomposition)
    [ConnectedSpace M.Carrier] [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier) :=
  exists_diffeomorph_standardThreeSphere_of_standardDecomposition (W := W)
    (hunitR := hunitR) (hunitL := hunitL) (hassoc := hassoc)
    (htransportL := Topology.connectedSum_transport_left_of_oppositeInvariance hop)
    (htransportR := Topology.connectedSum_transport_right_of_oppositeInvariance hop)
    (hsum := hsum)

theorem smoothPoincareConjecture_of_standardDecomposition_of_oppositeInvariance
    (hunitR : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum X
        Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hunitL : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum Topology.standardThreeSphereLift.{u} X
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hassoc : ∀ X Y Z : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum (Topology.connectedSum X Y) Z
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (Topology.connectedSum X (Topology.connectedSum Y Z)).toClosedOrientedManifold.Carrier))
    (hop : Topology.connectedSumOppositeInvariance.{u})
    (hsum : ∀ (H : FiniteSurgeryHistory.{u}) (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).componentConnectedSumStandardDecomposition)
    (hext : ∀ (M : Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)) :
    smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_standardDecomposition
    (hunitR := hunitR) (hunitL := hunitL) (hassoc := hassoc)
    (htransportL := Topology.connectedSum_transport_left_of_oppositeInvariance hop)
    (htransportR := Topology.connectedSum_transport_right_of_oppositeInvariance hop)
    (hsum := hsum) (hext := hext)

end DifferentialGeometry.PDE.RicciFlow.Surgery
