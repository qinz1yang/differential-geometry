import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundarySphereTransport

/-!
The same signed sphere patch passes through a right component and then a left component.
Both actual reconstructions preserve its full source and literal nested quotient square.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology

universe u
namespace GC.GraphManifold
variable (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary)
  (hD : D.kind = .withBoundary) [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier]

def boundaryCanonicalLeftDiffeomorph (K : CompactCarrier.{u}) (DK : K.Components)
    (hcut : K = C.withBoundarySum D hC hD)
    (hcomp : (hcut ▸ DK) = rawBoundarySumComponents C D hC hD)
    (i : Fin DK.count) (hi : i.val = 0) :
    C.Carrier ≃ₘ⟮C.model, (GC.Topology.componentCarrier K DK i).model⟯
      (GC.Topology.componentCarrier K DK i).Carrier := by
  subst K
  cases hcomp
  have hindex : i = rawBoundaryLeftIndex C D hC hD := Fin.ext hi
  subst i
  exact rawBoundaryLeftDiffeomorph C D hC hD

theorem boundaryCanonicalLeftDiffeomorph_apply (K : CompactCarrier.{u}) (DK : K.Components)
    (hcut : K = C.withBoundarySum D hC hD)
    (hcomp : (hcut ▸ DK) = rawBoundarySumComponents C D hC hD)
    (i : Fin DK.count) (hi : i.val = 0) (y : C.Carrier) :
    (boundaryCanonicalLeftDiffeomorph C D hC hD K DK hcut hcomp i hi y).val =
      hcut.symm ▸ (Sum.inl y : (C.withBoundarySum D hC hD).Carrier) := by
  subst K
  cases hcomp
  have hindex : i = rawBoundaryLeftIndex C D hC hD := Fin.ext hi
  subst i
  exact rawBoundaryLeftDiffeomorph_apply C D hC hD y

end GC.GraphManifold

namespace GC.GraphManifold
variable (C W D : CompactCarrier.{u}) (hC : C.kind = .withBoundary)
  (hW : W.kind = .withBoundary) (hD : D.kind = .withBoundary)
  [ConnectedSpace C.Carrier] [ConnectedSpace W.Carrier] [ConnectedSpace D.Carrier]
  {N : CompactCarrier.{u}} (hN : N.kind = .withBoundary) [ConnectedSpace N.Carrier]
  (T1 : TorusPresentation N) (hcut1 : T1.cutCarrier = C.withBoundarySum W hC hW)
  (hcomp1 : (hcut1 ▸ T1.components) = rawBoundarySumComponents C W hC hW)
  (i1 : Fin T1.components.count) (hi1 : i1.val = 1)
  (Q : ConnectedClosedOrientedManifold.{u} 3) (T2 : TorusPresentation (NoCuts.carrier Q))
  (hcut2 : T2.cutCarrier = N.withBoundarySum D hN hD)
  (hcomp2 : (hcut2 ▸ T2.components) = rawBoundarySumComponents N D hN hD)
  (i2 : Fin T2.components.count) (hi2 : i2.val = 0)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)

private def nestedBoundarySpherePoint : ClosureSphere.{u} × ℝ :=
  (Classical.arbitrary ClosureSphere, 0)

include hs in
omit [ConnectedSpace W.Carrier] in
private theorem nestedBoundarySpherePoint_mem : nestedBoundarySpherePoint.{u} ∈ d.source := by
  apply hs.symm.subset
  change (Classical.arbitrary ClosureSphere.{u}) ∈ (univ : Set ClosureSphere.{u}) ∧
    (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1
  exact ⟨mem_univ _, by norm_num⟩

private def nestedBoundarySphereFirst :
    PartialDiffeomorph sphereSignedCollarModel N.model (ClosureSphere.{u} × ℝ) N.Carrier ∞ :=
  boundaryTransportedPatch C W hC hW T1 hcut1 hcomp1 i1 hi1 sphereSignedCollarModel d
    nestedBoundarySpherePoint (nestedBoundarySpherePoint_mem W d hs) hI

omit [ConnectedSpace N.Carrier] in
private theorem nestedBoundarySphereFirst_source :
    (nestedBoundarySphereFirst C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI).source = d.source :=
  boundaryTransportedPatch_source C W hC hW T1 hcut1 hcomp1 i1 hi1 sphereSignedCollarModel d
    nestedBoundarySpherePoint (nestedBoundarySpherePoint_mem W d hs) hI

omit [ConnectedSpace N.Carrier] in
private theorem nestedBoundarySphereFirst_interior :
    (nestedBoundarySphereFirst C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI).target ⊆ N.interior :=
  boundaryTransportedPatch_interior C W hC hW T1 hcut1 hcomp1 i1 hi1 sphereSignedCollarModel d
    nestedBoundarySpherePoint (nestedBoundarySpherePoint_mem W d hs) hI

def nestedBoundarySpherePatch : PartialDiffeomorph sphereSignedCollarModel (𝓡 3)
  (ClosureSphere.{u} × ℝ) Q.Carrier ∞ :=
  T2.transportComponentPatch i2 N
    (boundaryCanonicalLeftDiffeomorph N D hN hD T2.cutCarrier T2.components
      hcut2 hcomp2 i2 hi2) sphereSignedCollarModel
    (nestedBoundarySphereFirst C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI)
    nestedBoundarySpherePoint
    ((nestedBoundarySphereFirst_source C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI).symm.subset
      (nestedBoundarySpherePoint_mem W d hs))
    (nestedBoundarySphereFirst_interior C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI)

local notation "dQ" => nestedBoundarySpherePatch C W D hC hW hD hN T1 hcut1 hcomp1 i1 hi1
  Q T2 hcut2 hcomp2 i2 hi2 d hs hI

theorem nestedBoundarySpherePatch_source : (dQ).source = d.source :=
  (T2.transportComponentPatch_source i2 N
    (boundaryCanonicalLeftDiffeomorph N D hN hD T2.cutCarrier T2.components
      hcut2 hcomp2 i2 hi2) sphereSignedCollarModel
    (nestedBoundarySphereFirst C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI)
    nestedBoundarySpherePoint
    ((nestedBoundarySphereFirst_source C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI).symm.subset
      (nestedBoundarySpherePoint_mem W d hs))
    (nestedBoundarySphereFirst_interior C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI)).trans
      (nestedBoundarySphereFirst_source C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI)

theorem nestedBoundarySpherePatch_full_source : (dQ).source = sphereSignedCollarSource :=
  (nestedBoundarySpherePatch_source C W D hC hW hD hN T1 hcut1 hcomp1 i1 hi1
    Q T2 hcut2 hcomp2 i2 hi2 d hs hI).trans hs

theorem nestedBoundarySpherePatch_interior : (dQ).target ⊆ (NoCuts.carrier Q).interior :=
  T2.transportComponentPatch_interior i2 N
    (boundaryCanonicalLeftDiffeomorph N D hN hD T2.cutCarrier T2.components
      hcut2 hcomp2 i2 hi2) sphereSignedCollarModel
    (nestedBoundarySphereFirst C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI)
    nestedBoundarySpherePoint
    ((nestedBoundarySphereFirst_source C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI).symm.subset
      (nestedBoundarySpherePoint_mem W d hs))
    (nestedBoundarySphereFirst_interior C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI)

theorem nestedBoundarySpherePatch_apply (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ sphereSignedCollarSource) :
    dQ p = T2.cutMap (hcut2.symm ▸ (Sum.inl
      (T1.cutMap (hcut1.symm ▸ (Sum.inr (d p) : (C.withBoundarySum W hC hW).Carrier))) :
        (N.withBoundarySum D hN hD).Carrier)) := by
  have hd1 : p ∈ (nestedBoundarySphereFirst C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI).source :=
    (nestedBoundarySphereFirst_source C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI).symm.subset
      (hs.symm.subset hp)
  have he1 := boundaryTransportedPatch_apply C W hC hW T1 hcut1 hcomp1 i1 hi1
    sphereSignedCollarModel d nestedBoundarySpherePoint (nestedBoundarySpherePoint_mem W d hs)
    hI p (hs.symm.subset hp)
  have he2 := T2.transportComponentPatch_apply i2 N
    (boundaryCanonicalLeftDiffeomorph N D hN hD T2.cutCarrier T2.components
      hcut2 hcomp2 i2 hi2) sphereSignedCollarModel
    (nestedBoundarySphereFirst C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI)
    nestedBoundarySpherePoint
    ((nestedBoundarySphereFirst_source C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI).symm.subset
      (nestedBoundarySpherePoint_mem W d hs))
    (nestedBoundarySphereFirst_interior C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI) p hd1
  have heLeft := boundaryCanonicalLeftDiffeomorph_apply N D hN hD T2.cutCarrier T2.components
    hcut2 hcomp2 i2 hi2 (nestedBoundarySphereFirst C W hC hW T1 hcut1 hcomp1 i1 hi1 d hs hI p)
  exact he2.trans ((congrArg T2.cutMap heLeft).trans
    (congrArg (fun y : N.Carrier => T2.cutMap
      (hcut2.symm ▸ (Sum.inl y : (N.withBoundarySum D hN hD).Carrier))) he1))

variable (E1 : BoundaryTori C 1) (EW : BoundaryTori W 2)
  (f1 : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hr1 : ReversesBoundaryOrientation (C.withBoundarySum W hC hW)
    (boundaryPortLeftCollar C W hC hW E1)
    (fun p => boundaryPortRightCollar C W hC hW EW 0 (f1 p.1, p.2)))
  (e1 : (boundaryPortPairing C W hC hW E1 EW f1 hr1).QuotientSpace ≃ₜ N.Carrier)
  (hsquare1 : ∀ a, e1 ((boundaryPortPairing C W hC hW E1 EW f1 hr1).quotientMap a) =
    T1.cutMap (hcut1.symm ▸ a))
  (EN : BoundaryTori N 1) (ED : BoundaryTori D 1)
  (f2 : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hr2 : ReversesBoundaryOrientation (N.withBoundarySum D hN hD)
    (boundaryPortLeftCollar N D hN hD EN)
    (fun p => boundaryPortRightCollar N D hN hD ED 0 (f2 p.1, p.2)))
  (e2 : (boundaryPortPairing N D hN hD EN ED f2 hr2).QuotientSpace ≃ₜ Q.Carrier)
  (hsquare2 : ∀ a, e2 ((boundaryPortPairing N D hN hD EN ED f2 hr2).quotientMap a) =
    T2.cutMap (hcut2.symm ▸ a))

include hsquare1 hsquare2 in
theorem nestedBoundarySpherePatch_square (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ sphereSignedCollarSource) :
    dQ p = e2 ((boundaryPortPairing N D hN hD EN ED f2 hr2).quotientMap
      (Sum.inl (e1 ((boundaryPortPairing C W hC hW E1 EW f1 hr1).quotientMap
        (Sum.inr (d p)))))) := by
  exact (nestedBoundarySpherePatch_apply C W D hC hW hD hN T1 hcut1 hcomp1 i1 hi1
    Q T2 hcut2 hcomp2 i2 hi2 d hs hI p hp).trans
    ((hsquare2 (Sum.inl (T1.cutMap
      (hcut1.symm ▸ (Sum.inr (d p) : (C.withBoundarySum W hC hW).Carrier))))).symm.trans
      (congrArg (fun y : N.Carrier => e2
        ((boundaryPortPairing N D hN hD EN ED f2 hr2).quotientMap (Sum.inl y)))
          (hsquare1 (Sum.inr (d p))).symm))

end GC.GraphManifold
