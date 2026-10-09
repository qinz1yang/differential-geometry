import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.NestedBoundarySphereTransport
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugPuncturedFactorBoundary

/-!
The same plug sphere has native coordinates after both physical boundary gluings.
Its fixed cap attachments retain the antipodal relation and both full half-collar squares.
-/

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology
universe u
namespace GC.GraphManifold

private def plugSphereIndex (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary)
    (hD : D.kind = .withBoundary) [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier]
    (K : CompactCarrier.{u}) (DK : K.Components)
    (hcut : K = C.withBoundarySum D hC hD)
    (hcomp : (hcut ▸ DK) = rawBoundarySumComponents C D hC hD) (right : Bool) :
    Fin DK.count := by
  subst K
  cases hcomp
  exact if right then rawBoundaryRightIndex C D hC hD else rawBoundaryLeftIndex C D hC hD

private theorem plugSphereIndex_val (C D : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier]
    (K : CompactCarrier.{u}) (DK : K.Components)
    (hcut : K = C.withBoundarySum D hC hD)
    (hcomp : (hcut ▸ DK) = rawBoundarySumComponents C D hC hD) (right : Bool) :
    (plugSphereIndex C D hC hD K DK hcut hcomp right).val = if right then 1 else 0 := by
  subst K
  cases hcomp
  cases right <;> rfl

variable (K0 W K1 : CompactCarrier.{u})
  (hK0 : K0.kind = .withBoundary) (hW : W.kind = .withBoundary)
  (hK1 : K1.kind = .withBoundary)
  [ConnectedSpace K0.Carrier] [ConnectedSpace W.Carrier] [ConnectedSpace K1.Carrier]
  {N : CompactCarrier.{u}} (hN : N.kind = .withBoundary) [ConnectedSpace N.Carrier]
  (T1 : TorusPresentation N) (hcut1 : T1.cutCarrier = K0.withBoundarySum W hK0 hW)
  (hcomp1 : (hcut1 ▸ T1.components) = rawBoundarySumComponents K0 W hK0 hW)
  (Q : ConnectedClosedOrientedManifold.{u} 3) (T2 : TorusPresentation (NoCuts.carrier Q))
  (hcut2 : T2.cutCarrier = N.withBoundarySum K1 hN hK1)
  (hcomp2 : (hcut2 ▸ T2.components) = rawBoundarySumComponents N K1 hN hK1)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)

private def plugSphereLift : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod (𝓘(ℝ)), sphereSignedCollarModel⟯
    (ClosureSphere.{u} × ℝ) :=
  (uliftDiffeomorph (I := 𝓡 2) (M := SphereTwo)).prodCongr (Diffeomorph.refl (𝓘(ℝ)) ℝ ∞)

private def plugSphereLiftedChart :=
  nestedBoundarySpherePatch K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1
    (plugSphereIndex K0 W hK0 hW T1.cutCarrier T1.components hcut1 hcomp1 true)
    (plugSphereIndex_val K0 W hK0 hW T1.cutCarrier T1.components hcut1 hcomp1 true)
    Q T2 hcut2 hcomp2
    (plugSphereIndex N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2 false)
    (plugSphereIndex_val N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2 false) d hs hI

def plugSphereCollarChart : PartialDiffeomorph ((𝓡 2).prod (𝓘(ℝ))) (𝓡 3)
    (SphereTwo × ℝ) Q.Carrier ∞ :=
  plugSphereLift.toPartialDiffeomorph.trans
    (plugSphereLiftedChart K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1 Q T2 hcut2 hcomp2 d hs hI)

local notation "qN" => plugSphereCollarChart K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1
  Q T2 hcut2 hcomp2 d hs hI

private theorem plugSphereLiftedChart_source :
    (plugSphereLiftedChart K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1
      Q T2 hcut2 hcomp2 d hs hI).source = sphereSignedCollarSource :=
  nestedBoundarySpherePatch_full_source K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1
    (plugSphereIndex K0 W hK0 hW T1.cutCarrier T1.components hcut1 hcomp1 true)
    (plugSphereIndex_val K0 W hK0 hW T1.cutCarrier T1.components hcut1 hcomp1 true)
    Q T2 hcut2 hcomp2
    (plugSphereIndex N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2 false)
    (plugSphereIndex_val N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2 false) d hs hI

theorem plugSphereCollarChart_source : (qN).source = univ ×ˢ Ioo (-1) 1 := by
  ext p
  change (p ∈ univ ∧ (ULift.up p.1, p.2) ∈
    (plugSphereLiftedChart K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1
      Q T2 hcut2 hcomp2 d hs hI).source) ↔ p ∈ univ ×ˢ Ioo (-1) 1
  rw [plugSphereLiftedChart_source]
  simp only [sphereSignedCollarSource, mem_univ, mem_prod, mem_Ioo, true_and]

theorem plugSphereCollarChart_apply (z : SphereTwo) (s : ℝ) (hs0 : -1 < s) (hs1 : s < 1) :
    qN (z, s) = T2.cutMap (hcut2.symm ▸ (Sum.inl
      (T1.cutMap (hcut1.symm ▸ (Sum.inr (d (ULift.up z, s)) :
        (K0.withBoundarySum W hK0 hW).Carrier))) :
          (N.withBoundarySum K1 hN hK1).Carrier)) := by
  exact nestedBoundarySpherePatch_apply K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1
    (plugSphereIndex K0 W hK0 hW T1.cutCarrier T1.components hcut1 hcomp1 true)
    (plugSphereIndex_val K0 W hK0 hW T1.cutCarrier T1.components hcut1 hcomp1 true)
    Q T2 hcut2 hcomp2
    (plugSphereIndex N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2 false)
    (plugSphereIndex_val N K1 hN hK1 T2.cutCarrier T2.components hcut2 hcomp2 false)
    d hs hI (ULift.up z, s) ⟨mem_univ _, hs0, hs1⟩

end GC.GraphManifold

namespace GC.Seifert.ElementaryPresentation
variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))
  (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)

local notation "Bᵢ" i => E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "Kᵢ" i => E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "uᵢ" i => E.plugCutFactor h hlin d hs heq hc hn i

def plugSphereAttaching (i : Fin 2) : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo :=
  (uliftDiffeomorph (I := 𝓡 2) (M := SphereTwo)).trans ((Kᵢ i).attaching 0) |>.trans
    (uliftDiffeomorph (I := 𝓡 2) (M := SphereTwo)).symm

local notation "aᵢ" i => E.plugSphereAttaching h hlin d hs hI heq hc hn hρ hρ1 havρ i

theorem plugSphereAttaching_up (i : Fin 2) (z : SphereTwo) :
    ULift.up ((aᵢ i) z) = (Kᵢ i).attaching 0 (ULift.up z) := ULift.up_down _

theorem plugSphereAttaching_antipodal (z : SphereTwo) :
    (aᵢ (1 : Fin 2)) (boundaryAttachment.1 z) = (aᵢ (0 : Fin 2)) z := by
  apply ULift.up_injective
  rw [E.plugSphereAttaching_up, E.plugSphereAttaching_up]
  have ha := E.plugPuncturedFactor_attaching_antipodal h hlin d hs hI heq hc hn
    hρ hρ1 havρ (ULift.up z)
  exact ((Kᵢ (1 : Fin 2)).attaching 0).apply_symm_apply ((Kᵢ (0 : Fin 2)).attaching 0
    (ULift.up z)) |>.symm.trans (congrArg ((Kᵢ (1 : Fin 2)).attaching 0) ha) |>.symm

private theorem plugSphereHalf_fold (i : Fin 2)
    (p : ClosureSphere.{u} × EuclideanHalfSpace 1) (hp : p ∈ sphereHalfCollarSource) :
    (uᵢ i) ((Bᵢ i).sphere 0 p) = d (sphereCutHalfSigned (sphereCutBoundarySide i) p) := by
  change sphereCutFold (boundedPlugCutCollars d) (((Bᵢ i).sphere 0 p).val) = _
  rw [E.plugSideBoundary_sphere_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i p hp]
  exact sphereCutFullCollar_fold (boundedPlugCutCollars d)
    (boundedPlugCutCollars_source d hs) (boundedPlugCutCollars_disjoint d)
    0 (sphereCutBoundarySide i) p hp

variable (K0 K1 : CompactCarrier.{u}) (hK0 : K0.kind = .withBoundary)
  (hW : W.kind = .withBoundary) (hK1 : K1.kind = .withBoundary)
  [ConnectedSpace K0.Carrier] [ConnectedSpace W.Carrier] [ConnectedSpace K1.Carrier]
  {N : CompactCarrier.{u}} (hN : N.kind = .withBoundary) [ConnectedSpace N.Carrier]
  (T1 : TorusPresentation N) (hcut1 : T1.cutCarrier = K0.withBoundarySum W hK0 hW)
  (hcomp1 : (hcut1 ▸ T1.components) = rawBoundarySumComponents K0 W hK0 hW)
  (Q : ConnectedClosedOrientedManifold.{u} 3) (T2 : TorusPresentation (NoCuts.carrier Q))
  (hcut2 : T2.cutCarrier = N.withBoundarySum K1 hN hK1)
  (hcomp2 : (hcut2 ▸ T2.components) = rawBoundarySumComponents N K1 hN hK1)

local notation "qN" => plugSphereCollarChart K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1
  Q T2 hcut2 hcomp2 d hs hI
private def plugSphereNestedFold (x : W.Carrier) : Q.Carrier :=
  T2.cutMap (hcut2.symm ▸ (Sum.inl
    (T1.cutMap (hcut1.symm ▸ (Sum.inr x : (K0.withBoundarySum W hK0 hW).Carrier))) :
      (N.withBoundarySum K1 hN hK1).Carrier))

local notation "foldN" => plugSphereNestedFold K0 K1 hK0 hW hK1 hN T1 hcut1 Q T2 hcut2

include heq hc hn havρ in
theorem plugSphereCollarChart_positive (z : SphereTwo) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : 2 * s < 1) :
    qN ((aᵢ (0 : Fin 2)) z, 2 * s) = foldN ((uᵢ (0 : Fin 2))
      ((Bᵢ (0 : Fin 2)).sphere 0
        ((Kᵢ (0 : Fin 2)).attaching 0 (ULift.up z), halfPoint (2 * s) (by positivity)))) := by
  rw [plugSphereCollarChart_apply K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1
    Q T2 hcut2 hcomp2 d hs hI ((aᵢ (0 : Fin 2)) z) (2 * s) (by linarith) hs1]
  rw [E.plugSphereAttaching_up]
  exact congrArg (foldN) (E.plugSphereHalf_fold h hlin d hs hI heq hc hn hρ hρ1 havρ (0 : Fin 2)
    ((Kᵢ (0 : Fin 2)).attaching 0 (ULift.up z), halfPoint (2 * s) (by positivity))
    hs1).symm

include heq hc hn havρ in
theorem plugSphereCollarChart_negative (z : SphereTwo) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : 2 * s < 1) :
    qN ((aᵢ (1 : Fin 2)) z, -(2 * s)) = foldN ((uᵢ (1 : Fin 2))
      ((Bᵢ (1 : Fin 2)).sphere 0
        ((Kᵢ (1 : Fin 2)).attaching 0 (ULift.up z), halfPoint (2 * s) (by positivity)))) := by
  rw [plugSphereCollarChart_apply K0 W K1 hK0 hW hK1 hN T1 hcut1 hcomp1
    Q T2 hcut2 hcomp2 d hs hI ((aᵢ (1 : Fin 2)) z) (-(2 * s)) (by linarith) (by linarith)]
  rw [E.plugSphereAttaching_up]
  exact congrArg (foldN) (E.plugSphereHalf_fold h hlin d hs hI heq hc hn hρ hρ1 havρ (1 : Fin 2)
    ((Kᵢ (1 : Fin 2)).attaching 0 (ULift.up z), halfPoint (2 * s) (by positivity))
    hs1).symm

end GC.Seifert.ElementaryPresentation
