import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawBoundaryAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawClosedBoundaryGluing
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryReversalFoldTransport

/-!
Two actual boundary gluings retain their same quotient maps and raw witnesses.
The second gluing shrinks both sides by the first width, preserving the physical normal coordinate.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology
universe u
namespace GC.GraphManifold

private theorem doubleExternal_collar {N : CompactCarrier.{u}} {n : ℕ} (E : BoundaryTori N n)
    (hn : n = 1) (i : Fin 1) (p : Torus × EuclideanHalfSpace 1) :
    ((hn ▸ E : BoundaryTori N 1).collar i p) = E.collar (Fin.cast hn.symm i) p := by
  cases hn
  rfl

private theorem doubleExternal_image {N : CompactCarrier.{u}} {n : ℕ} (E : BoundaryTori N n)
    (hn : n = 1) : (hn ▸ E : BoundaryTori N 1).image = E.image := by
  cases hn
  rfl

variable (C W D : CompactCarrier.{u})
  (hC : C.kind = .withBoundary) (hW : W.kind = .withBoundary)
  (hD : D.kind = .withBoundary)
  [ConnectedSpace C.Carrier] [ConnectedSpace W.Carrier] [ConnectedSpace D.Carrier]
  (ΓC : BoundaryTori C 1) (EW : BoundaryTori W 2) (ΓD : BoundaryTori D 1)
  (hbC : C.model.boundary C.Carrier = ΓC.image)
  (hbW : W.model.boundary W.Carrier = EW.image)
  (hbD : D.model.boundary D.Carrier = ΓD.image)
  (f0 f1 : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hr0 : ReversesBoundaryOrientation (C.withBoundarySum W hC hW)
    (boundaryPortLeftCollar C W hC hW ΓC)
    (fun p => boundaryPortRightCollar C W hC hW EW 0 (f0 p.1, p.2)))
  (hr1 : ReversesBoundaryOrientation (D.withBoundarySum W hD hW)
    (boundaryPortLeftCollar D W hD hW ΓD)
    (fun p => boundaryPortRightCollar D W hD hW EW 1 (f1 p.1, p.2)))

include hbC hbW hbD hr1 in
theorem exists_plugDoubleBoundaryAssembly
    (RC : RawGraphPresentation C) (RW : RawGraphPresentation W) (RD : RawGraphPresentation D) :
    ∃ (N : CompactCarrier.{u}) (hN : N.kind = .withBoundary) (hconn : ConnectedSpace N.Carrier)
      (T1 : TorusPresentation N) (δ1 : ℝ) (hδ1 : 0 < δ1) (hδ11 : δ1 ≤ 1)
      (hcut1 : T1.cutCarrier = C.withBoundarySum W hC hW),
      (hcut1 ▸ T1.components) = rawBoundarySumComponents C W hC hW ∧
      (hcut1 ▸ T1.pairing) = (boundaryPortPairing C W hC hW ΓC EW f0 hr0).shrink hδ1 hδ11 ∧
      ∃ hn : T1.externalCount = 1,
      let EN : BoundaryTori N 1 := hn ▸ T1.external
      let : ConnectedSpace N.Carrier := hconn
      ∃ (e1 : (boundaryPortPairing C W hC hW ΓC EW f0 hr0).QuotientSpace ≃ₜ N.Carrier)
        (hr2 : ReversesBoundaryOrientation (N.withBoundarySum D hN hD)
          (boundaryPortLeftCollar N D hN hD EN)
          (fun p => boundaryPortRightCollar N D hN hD (ΓD.shrink hδ1 hδ11) 0
            (f1.symm p.1, p.2))),
      (∀ x, e1 ((boundaryPortPairing C W hC hW ΓC EW f0 hr0).quotientMap x) =
        T1.cutMap (hcut1.symm ▸ x)) ∧
      (∀ p, p ∈ halfCollarSource → EN.collar 0 p =
        T1.cutMap (hcut1.symm ▸ Sum.inr (EW.collar 1 (p.1, halfSpaceScale hδ1 p.2)))) ∧
      ∃ (δ2 : ℝ) (hδ2 : 0 < δ2) (hδ21 : δ2 ≤ 1)
        (Q : ConnectedClosedOrientedManifold.{u} 3) (T2 : TorusPresentation (NoCuts.carrier Q))
        (hcut2 : T2.cutCarrier = N.withBoundarySum D hN hD),
        (hcut2 ▸ T2.components) = rawBoundarySumComponents N D hN hD ∧
        (hcut2 ▸ T2.pairing) =
          (boundaryPortPairing N D hN hD EN (ΓD.shrink hδ1 hδ11) f1.symm hr2).shrink
            hδ2 hδ21 ∧ T2.externalCount = 0 ∧
        Nonempty (RawGraphPresentation (NoCuts.carrier Q)) ∧
        ∃ e2 : (boundaryPortPairing N D hN hD EN (ΓD.shrink hδ1 hδ11)
          f1.symm hr2).QuotientSpace ≃ₜ Q.Carrier,
          ∀ x, e2 ((boundaryPortPairing N D hN hD EN (ΓD.shrink hδ1 hδ11)
            f1.symm hr2).quotientMap x) = T2.cutMap (hcut2.symm ▸ x) := by
  obtain ⟨N, hN, hconn, T1, δ1, hδ1, hδ11, hcut1, hn, hc, hcomponents, hpairing,
    hexternal, hpc, hmatching, howners, hexowners, eC, eW, hposC, hposW,
    e1, hsquare1, hport, R, ε, hε, hε1, GN, hGN, edge, hGport, hold, hmatch⟩ :=
    exists_rawBoundaryAssembly C W hC hW ΓC EW f0 hr0 hbC hbW RC RW
  let : ConnectedSpace N.Carrier := hconn
  let EN : BoundaryTori N 1 := hn ▸ T1.external
  have hp : ∀ p, p ∈ halfCollarSource → EN.collar 0 p =
      T1.cutMap (hcut1.symm ▸ Sum.inr (EW.collar 1 (p.1, halfSpaceScale hδ1 p.2))) := by
    intro p hp
    rw [doubleExternal_collar T1.external hn, hport 0 p hp]
    exact hsquare1 _
  have hr2 := firstQuotientSecondFold_reversal C W D N hC hW hD hN T1 hcut1
    ΓD EW EN hδ1 hδ11 f1 hp hr1
  have hbN := T1.external_exhausted.trans (doubleExternal_image T1.external hn).symm
  have hbDs : D.model.boundary D.Carrier = (ΓD.shrink hδ1 hδ11).image :=
    hbD.trans (ΓD.shrink_image hδ1 hδ11).symm
  obtain ⟨δ2, hδ2, hδ21, Q, T2, hcut2, hcomp2, hpair2, hzero, hraw, e2, hsquare2⟩ :=
    exists_closedRawBoundaryGluing N D hN hD GN RD EN (ΓD.shrink hδ1 hδ11)
      hbN hbDs f1.symm hr2
  exact ⟨N, hN, hconn, T1, δ1, hδ1, hδ11, hcut1, hcomponents, hpairing, hn,
    e1, hr2, hsquare1, hp, δ2, hδ2, hδ21, Q, T2, hcut2, hcomp2, hpair2,
    hzero, hraw, e2, hsquare2⟩

end GC.GraphManifold
