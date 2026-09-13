import DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportConnected

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

def connectedSumOppositeInvariance : Prop :=
  (∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty ((connectedSum X.opposite Y).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum X Y).toClosedOrientedManifold.Carrier)) ∧
  (∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty ((connectedSum X Y.opposite).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum X Y).toClosedOrientedManifold.Carrier))

theorem connectedSumOppositeInvariance_of_transport
    (htransportL : ∀ X X' Y : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (X.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        X'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X' Y).toClosedOrientedManifold.Carrier))
    (htransportR : ∀ X Y Y' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Y.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        Y'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X Y').toClosedOrientedManifold.Carrier)) :
    connectedSumOppositeInvariance.{u} :=
  ⟨fun X Y => htransportL X.opposite X Y ⟨Diffeomorph.refl (𝓡 3) X.Carrier ∞⟩,
    fun X Y => htransportR X Y.opposite Y ⟨Diffeomorph.refl (𝓡 3) Y.Carrier ∞⟩⟩

theorem connectedSum_transport_left_of_oppositeInvariance
    (h : connectedSumOppositeInvariance.{u}) :
    ∀ X X' Y : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (X.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        X'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X' Y).toClosedOrientedManifold.Carrier) := by
  intro X X' Y hX
  obtain ⟨Φ⟩ := hX
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite
    Φ X.orientation X'.orientation with hΦ | hΦ
  · exact connectedSum_transport_left_holds X X' Y Φ hΦ
  · obtain ⟨f⟩ := connectedSum_transport_left_holds X X'.opposite Y Φ hΦ
    obtain ⟨g⟩ := h.1 X' Y
    exact ⟨f.trans g⟩

theorem connectedSum_transport_right_of_oppositeInvariance
    (h : connectedSumOppositeInvariance.{u}) :
    ∀ X Y Y' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Y.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        Y'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X Y').toClosedOrientedManifold.Carrier) := by
  intro X Y Y' hY
  obtain ⟨Ψ⟩ := hY
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite
    Ψ Y.orientation Y'.orientation with hΨ | hΨ
  · exact connectedSum_transport_right_holds X Y Y' Ψ hΨ
  · obtain ⟨f⟩ := connectedSum_transport_right_holds X Y Y'.opposite Ψ hΨ
    obtain ⟨g⟩ := h.2 X Y'
    exact ⟨f.trans g⟩

end DifferentialGeometry.Topology
