import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgery

/-!
Actual oriented closed quotients of torus pairings, with the source-piece circle fibrations.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

theorem exists_closedRawTorusQuotient (C : CompactCarrier.{u}) (D : C.Components)
    (F : ∀ i, CircleFibration C (D.piece i)) (P : TorusPairing C)
    (hb : C.model.boundary C.Carrier = ⋃ j, P.gluing.block j)
    [ConnectedSpace P.QuotientSpace] (left right : Fin P.count → Fin D.count)
    (hl : ∀ j, P.gluing.left j ⊆ D.piece (left j))
    (hr : ∀ j, P.gluing.right j ⊆ D.piece (right j)) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
      (Q : ConnectedClosedOrientedManifold.{u} 3)
      (G : RawGraphPresentation (NoCuts.carrier Q)) (hC : G.cutCarrier = C),
      (hC ▸ G.components) = D ∧ (hC ▸ G.pairing) = P.shrink hδ hδ1 ∧
      ∃ e : P.QuotientSpace ≃ₜ Q.Carrier,
        ∀ x : C.Carrier, e (P.quotientMap x) =
          G.reconstruction (G.pairing.quotientMap (hC.symm ▸ x)) := by
  obtain ⟨δ, hδ, hδ1, Q, T, hC, hD, hP, e, he⟩ :=
    exists_closedTorusQuotientPresentation C D P hb left right hl hr
  cases hC
  cases hD
  let G := T.withFibration F
  exact ⟨δ, hδ, hδ1, Q, G, rfl, rfl, hP, e, he⟩

end GC.GraphManifold
