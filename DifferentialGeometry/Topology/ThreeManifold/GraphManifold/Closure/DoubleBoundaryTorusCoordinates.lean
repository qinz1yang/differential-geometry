import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryGluingSeamCoordinates
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.NestedBoundarySphereTransport

/-!
The same two boundary gluings retain exact physical half coordinates in the final carrier.
The second physical collar has the product of both actual normal widths on each side.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology
universe u
namespace GC.GraphManifold

variable (N K1 : CompactCarrier.{u}) (hN : N.kind = .withBoundary)
  (hK1 : K1.kind = .withBoundary) [ConnectedSpace N.Carrier] [ConnectedSpace K1.Carrier]
  (Q : ConnectedClosedOrientedManifold.{u} 3) (T2 : TorusPresentation (NoCuts.carrier Q))
  (hcut2 : T2.cutCarrier = N.withBoundarySum K1 hN hK1)
  (hcomp2 : (hcut2 ▸ T2.components) = rawBoundarySumComponents N K1 hN hK1)

private def doubleLeftIndex (K : CompactCarrier.{u}) (DK : K.Components)
    (hcut : K = N.withBoundarySum K1 hN hK1)
    (hcomp : (hcut ▸ DK) = rawBoundarySumComponents N K1 hN hK1) : Fin DK.count := by
  subst K
  cases hcomp
  exact rawBoundaryLeftIndex N K1 hN hK1

private theorem doubleLeftIndex_val (K : CompactCarrier.{u}) (DK : K.Components)
    (hcut : K = N.withBoundarySum K1 hN hK1)
    (hcomp : (hcut ▸ DK) = rawBoundarySumComponents N K1 hN hK1) :
    (doubleLeftIndex N K1 hN hK1 K DK hcut hcomp).val = 0 := by
  subst K
  cases hcomp
  rfl

private def doubleLeftDiffeomorph :=
  boundaryCanonicalLeftDiffeomorph N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2
    (doubleLeftIndex N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2)
    (doubleLeftIndex_val N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2)

variable (T1 : TorusPresentation N) (j1 : Fin T1.pairing.count)

omit [ConnectedSpace N.Carrier] in
private theorem doubleSeamBase_mem : (torusBase, (0 : ℝ)) ∈ (T1.seam j1).source := by
  rw [T1.seam_source]
  exact ⟨by norm_num, by norm_num⟩

def doubleBoundaryLeftSeamChart :
    PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) Q.Carrier ∞ :=
  T2.transportComponentPatch
    (doubleLeftIndex N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2) N
    (doubleLeftDiffeomorph N K1 hN hK1 Q T2 hcut2 hcomp2) signedCollarModel
    (T1.seam j1) (torusBase, 0) (doubleSeamBase_mem N T1 j1) (T1.seam_interior j1)

local notation "qL" => doubleBoundaryLeftSeamChart N K1 hN hK1 Q T2 hcut2 hcomp2 T1 j1

theorem doubleBoundaryLeftSeamChart_source : (qL).source = signedCollarSource :=
  (T2.transportComponentPatch_source
    (doubleLeftIndex N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2) N
    (doubleLeftDiffeomorph N K1 hN hK1 Q T2 hcut2 hcomp2) signedCollarModel
    (T1.seam j1) (torusBase, 0) (doubleSeamBase_mem N T1 j1)
    (T1.seam_interior j1)).trans (T1.seam_source j1)

theorem doubleBoundaryLeftSeamChart_apply (p : Torus × ℝ) (hp : p ∈ signedCollarSource) :
    qL p = T2.cutMap (hcut2.symm ▸ Sum.inl (T1.seam j1 p)) := by
  have he := T2.transportComponentPatch_apply
    (doubleLeftIndex N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2) N
    (doubleLeftDiffeomorph N K1 hN hK1 Q T2 hcut2 hcomp2) signedCollarModel
    (T1.seam j1) (torusBase, 0) (doubleSeamBase_mem N T1 j1)
    (T1.seam_interior j1) p ((T1.seam_source j1).symm.subset hp)
  have hv := boundaryCanonicalLeftDiffeomorph_apply N K1 hN hK1 T2.cutCarrier T2.components
    hcut2 hcomp2 (doubleLeftIndex N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2)
    (doubleLeftIndex_val N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2) (T1.seam j1 p)
  exact he.trans (congrArg T2.cutMap hv)

end GC.GraphManifold

namespace GC.GraphManifold
variable (K0 W K1 : CompactCarrier.{u})
  (hK0 : K0.kind = .withBoundary) (hW : W.kind = .withBoundary)
  (hK1 : K1.kind = .withBoundary)
  [ConnectedSpace K0.Carrier] [ConnectedSpace W.Carrier] [ConnectedSpace K1.Carrier]
  {N : CompactCarrier.{u}} (hN : N.kind = .withBoundary) [ConnectedSpace N.Carrier]
  (T1 : TorusPresentation N) (hcut1 : T1.cutCarrier = K0.withBoundarySum W hK0 hW)
  (Γ0 : BoundaryTori K0 1) (EW : BoundaryTori W 2) (Γ1 : BoundaryTori K1 1)
  (f0 f1 : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hr0 : ReversesBoundaryOrientation (K0.withBoundarySum W hK0 hW)
    (boundaryPortLeftCollar K0 W hK0 hW Γ0)
    (fun p => boundaryPortRightCollar K0 W hK0 hW EW 0 (f0 p.1, p.2)))
  {δ1 : ℝ} (hδ1 : 0 < δ1) (hδ11 : δ1 ≤ 1)
  (hpair1 : (hcut1 ▸ T1.pairing) =
    (boundaryPortPairing K0 W hK0 hW Γ0 EW f0 hr0).shrink hδ1 hδ11)
  (EN : BoundaryTori N 1)
  (hport : ∀ p, p ∈ halfCollarSource → EN.collar 0 p =
    T1.cutMap (hcut1.symm ▸ Sum.inr (EW.collar 1 (p.1, halfSpaceScale hδ1 p.2))))
  (hr2 : ReversesBoundaryOrientation (N.withBoundarySum K1 hN hK1)
    (boundaryPortLeftCollar N K1 hN hK1 EN)
    (fun p => boundaryPortRightCollar N K1 hN hK1 (Γ1.shrink hδ1 hδ11) 0
      (f1.symm p.1, p.2)))
  (Q : ConnectedClosedOrientedManifold.{u} 3) (T2 : TorusPresentation (NoCuts.carrier Q))
  (hcut2 : T2.cutCarrier = N.withBoundarySum K1 hN hK1)
  (hcomp2 : (hcut2 ▸ T2.components) = rawBoundarySumComponents N K1 hN hK1)
  {δ2 : ℝ} (hδ2 : 0 < δ2) (hδ21 : δ2 ≤ 1)
  (hpair2 : (hcut2 ▸ T2.pairing) =
    (boundaryPortPairing N K1 hN hK1 EN (Γ1.shrink hδ1 hδ11) f1.symm hr2).shrink hδ2 hδ21)

private theorem doubleDepth_halfPoint {s : ℝ} (hs : 0 ≤ s) :
    halfSpaceScale hδ1 (halfPoint (s / δ1) (div_nonneg hs hδ1.le)) = halfPoint s hs := by
  apply Subtype.ext
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  rw [halfSpaceScale_coord]
  change δ1 * (s / δ1) = s
  exact mul_div_cancel₀ s hδ1.ne'

include hpair1 hport hpair2 in
theorem exists_doubleBoundaryTorusCoordinates :
    ∃ (j1 : Fin T1.pairing.count) (j2 : Fin T2.pairing.count),
      T1.pairing.matching j1 = f0 ∧ T2.pairing.matching j2 = f1.symm ∧
      let qL := doubleBoundaryLeftSeamChart N K1 hN hK1 Q T2 hcut2 hcomp2 T1 j1
      let qR := seamFlipChart f1.symm (T2.seam j2)
      qL.source = signedCollarSource ∧ qR.source = signedCollarSource ∧
      (∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < δ1 →
        qL (t, -(s / δ1)) = T2.cutMap (hcut2.symm ▸ Sum.inl
          (T1.cutMap (hcut1.symm ▸ Sum.inl (Γ0.collar 0 (t, halfPoint s hs)))))) ∧
      (∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < δ1 →
        qL (t, s / δ1) = T2.cutMap (hcut2.symm ▸ Sum.inl
          (T1.cutMap (hcut1.symm ▸ Sum.inr (EW.collar 0 (f0 t, halfPoint s hs)))))) ∧
      (∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < δ1 * δ2 →
        qR (t, -(s / (δ1 * δ2))) =
          T2.cutMap (hcut2.symm ▸ Sum.inr (Γ1.collar 0 (t, halfPoint s hs)))) ∧
      ∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < δ1 * δ2 →
        qR (t, s / (δ1 * δ2)) = T2.cutMap (hcut2.symm ▸ Sum.inl
          (T1.cutMap (hcut1.symm ▸ Sum.inr (EW.collar 1 (f1 t, halfPoint s hs))))) := by
  obtain ⟨j1, hm1, hL1, hR1⟩ := exists_boundaryGluingSeamCoordinates K0 W hK0 hW
    Γ0 EW f0 hr0 hδ1 hδ11 T1 hcut1 hpair1
  obtain ⟨j2, hm2, hL2, hR2⟩ := exists_boundaryGluingSeamCoordinates N K1 hN hK1
    EN (Γ1.shrink hδ1 hδ11) f1.symm hr2 hδ2 hδ21 T2 hcut2 hpair2
  refine ⟨j1, j2, hm1, hm2,
    doubleBoundaryLeftSeamChart_source N K1 hN hK1 Q T2 hcut2 hcomp2 T1 j1,
    seamFlipChart_source f1.symm (T2.seam j2) (T2.seam_source j2), ?_, ?_, ?_, ?_⟩
  · intro t s hs hlt
    have hd0 : 0 ≤ s / δ1 := div_nonneg hs hδ1.le
    have hd1 : s / δ1 < 1 := (div_lt_one hδ1).mpr hlt
    rw [doubleBoundaryLeftSeamChart_apply N K1 hN hK1 Q T2 hcut2 hcomp2 T1 j1
      (t, -(s / δ1)) ⟨by linarith, by linarith⟩, hL1 t s hs hlt]
  · intro t s hs hlt
    have hd0 : 0 ≤ s / δ1 := div_nonneg hs hδ1.le
    have hd1 : s / δ1 < 1 := (div_lt_one hδ1).mpr hlt
    rw [doubleBoundaryLeftSeamChart_apply N K1 hN hK1 Q T2 hcut2 hcomp2 T1 j1
      (t, s / δ1) ⟨by linarith, by linarith⟩, hR1 t s hs hlt]
  · intro t s hs hlt
    have hd0 : 0 ≤ s / δ1 := div_nonneg hs hδ1.le
    have hd2 : s / δ1 < δ2 := (div_lt_iff₀ hδ1).mpr (by nlinarith)
    simp only [seamFlipChart_apply, neg_neg]
    change T2.seam j2 (f1 t, s / (δ1 * δ2)) = _
    rw [← div_div, hR2 (f1 t) (s / δ1) hd0 hd2, f1.symm_apply_apply,
      BoundaryTori.shrink_collar_apply, doubleDepth_halfPoint hδ1 hs]
  · intro t s hs hlt
    have hd0 : 0 ≤ s / δ1 := div_nonneg hs hδ1.le
    have hd2 : s / δ1 < δ2 := (div_lt_iff₀ hδ1).mpr (by nlinarith)
    have hp : (f1 t, halfPoint (s / δ1) hd0) ∈ halfCollarSource := by
      change s / δ1 < 1
      exact hd2.trans_le hδ21
    simp only [seamFlipChart_apply]
    change T2.seam j2 (f1 t, -(s / (δ1 * δ2))) = _
    rw [← div_div, hL2 (f1 t) (s / δ1) hd0 hd2, hport _ hp,
      doubleDepth_halfPoint hδ1 hs]

end GC.GraphManifold
