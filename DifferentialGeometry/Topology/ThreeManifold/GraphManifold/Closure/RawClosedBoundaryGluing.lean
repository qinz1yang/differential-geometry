import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawBoundaryGluing

/-!
Actual closed gluing of two bounded raw carriers through their genuine boundary-port pairing,
with the closed quotient atlas, orientation and local raw refinement.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable (C D : CompactCarrier.{u})
  (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
  [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier]

set_option backward.isDefEq.respectTransparency false in
private theorem rawClosedBoundaryPieces
    (K : CompactCarrier.{u}) (DK : K.Components)
    (hcut : K = C.withBoundarySum D hC hD)
    (hcomponents : (hcut ▸ DK) = rawBoundarySumComponents C D hC hD)
    (RC : RawGraphPresentation C) (RD : RawGraphPresentation D) :
    ∀ i, Nonempty (RawGraphPresentation (GC.Topology.componentCarrier K DK i)) := by
  subst K
  cases hcomponents
  intro i
  have hi : i.val < 2 := i.isLt
  have hcases : i = rawBoundaryLeftIndex C D hC hD ∨
      i = rawBoundaryRightIndex C D hC hD := by
    by_cases hzero : i.val = 0
    · exact Or.inl (Fin.ext hzero)
    · exact Or.inr (Fin.ext (by change i.val = 1; omega))
  rcases hcases with rfl | rfl
  · exact ⟨RC.transport (rawBoundaryLeftDiffeomorph C D hC hD)
      (rawBoundaryLeftDiffeomorph_positive C D hC hD)⟩
  · exact ⟨RD.transport (rawBoundaryRightDiffeomorph C D hC hD)
      (rawBoundaryRightDiffeomorph_positive C D hC hD)⟩

set_option backward.isDefEq.respectTransparency false in
theorem exists_closedRawBoundaryGluing
    (RC : RawGraphPresentation C) (RD : RawGraphPresentation D)
    (E1 : BoundaryTori C 1) (E2 : BoundaryTori D 1)
    (hbC : C.model.boundary C.Carrier = E1.image)
    (hbD : D.model.boundary D.Carrier = E2.image)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hrev : ReversesBoundaryOrientation (C.withBoundarySum D hC hD)
      (boundaryPortLeftCollar C D hC hD E1)
      (fun p => boundaryPortRightCollar C D hC hD E2 0 (f p.1, p.2))) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
      (Q : ConnectedClosedOrientedManifold.{u} 3)
      (T : TorusPresentation (NoCuts.carrier Q))
      (hcut : T.cutCarrier = C.withBoundarySum D hC hD),
      (hcut ▸ T.components) = rawBoundarySumComponents C D hC hD ∧
      (hcut ▸ T.pairing) =
        (boundaryPortPairing C D hC hD E1 E2 f hrev).shrink hδ hδ1 ∧
      T.externalCount = 0 ∧
      Nonempty (RawGraphPresentation (NoCuts.carrier Q)) ∧
      ∃ e : (boundaryPortPairing C D hC hD E1 E2 f hrev).QuotientSpace ≃ₜ Q.Carrier,
        ∀ x : (C.withBoundarySum D hC hD).Carrier,
          e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap x) =
            T.cutMap (hcut.symm ▸ x) := by
  let P := boundaryPortPairing C D hC hD E1 E2 f hrev
  let := rawBoundaryQuotient_connected C D hC hD E1 E2 f hrev
  have hb : (C.withBoundarySum D hC hD).model.boundary
      (C.withBoundarySum D hC hD).Carrier = ⋃ j, P.gluing.block j := by
    have h := boundaryPortPairing_boundary C D hC hD E1 E2 f hrev hbC hbD
    simpa only [BoundaryTori.image, iUnion_of_empty, union_empty] using h
  obtain ⟨δ, hδ, hδ1, Q, T, hcut, hcomponents, hpairing, e, hsquare⟩ :=
    exists_closedTorusQuotientPresentation (C.withBoundarySum D hC hD)
      (rawBoundarySumComponents C D hC hD) P hb
      (fun j => rawBoundaryLeftIndex C D hC hD)
      (fun j => rawBoundaryRightIndex C D hC hD)
      (rawBoundaryPairing_left_owned C D hC hD E1 E2 f hrev)
      (rawBoundaryPairing_right_owned C D hC hD E1 E2 f hrev)
  let R : ∀ i, RawGraphPresentation (T.Component i) := fun i =>
    Classical.choice
      (rawClosedBoundaryPieces C D hC hD T.cutCarrier T.components hcut hcomponents RC RD i)
  exact ⟨δ, hδ, hδ1, Q, T, hcut, hcomponents, hpairing, T.externalCount_eq_zero,
    exists_rawGraphPresentation_of_rawPieces T R, e, hsquare⟩

end GC.GraphManifold
