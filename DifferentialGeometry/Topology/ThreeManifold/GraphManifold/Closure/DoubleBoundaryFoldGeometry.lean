import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryReversalFoldTransport

/-!
The same two boundary quotients give three whole physical maps into the final carrier.
Each map is smooth and preserves the actual orientation through its complete differential.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

theorem doubleBoundaryFold_comp_positive {A B C : CompactCarrier.{u}}
    {f : B.Carrier → C.Carrier} {g : A.Carrier → B.Carrier}
    (hsf : ContMDiff B.model C.model ∞ f) (hsg : ContMDiff A.model B.model ∞ g)
    (hf : IsOrientedFold f) (hg : IsOrientedFold g) : IsOrientedFold (f ∘ g) := by
  intro x
  obtain ⟨L, hL, hoL⟩ := hg x
  obtain ⟨R, hR, hoR⟩ := hf (g x)
  refine ⟨L.trans R, ?_, ?_⟩
  · intro v
    change R (L v) = _
    rw [hR, hL]
    exact (mfderiv_comp_apply x (hsf.mdifferentiable (by simp) _)
      (hsg.mdifferentiable (by simp) _) v).symm
  · exact (orientation_map_trans_fin_three L R _).trans
      ((congrArg (Orientation.map (Fin 3) R) hoL).trans hoR)

private theorem doubleFoldInl_smooth (C D : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary) :
    ContMDiff C.model (C.withBoundarySum D hC hD).model ∞
      (Sum.inl : C.Carrier → (C.withBoundarySum D hC hD).Carrier) := by
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      exact ContMDiff.inl

private theorem doubleFoldInr_smooth (C D : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary) :
    ContMDiff D.model (C.withBoundarySum D hC hD).model ∞
      (Sum.inr : D.Carrier → (C.withBoundarySum D hC hD).Carrier) := by
  cases C with
  | mk k A O =>
    cases D with
    | mk l B O' =>
      cases hC
      cases hD
      exact ContMDiff.inr

private theorem doubleFoldCut_smooth {A Q : CompactCarrier.{u}}
    (T : TorusPresentation Q) (he : A = T.cutCarrier) :
    ContMDiff A.model Q.model ∞ (fun x : A.Carrier => T.cutMap (he ▸ x)) := by
  cases he
  exact T.quotient_smooth

private theorem doubleFoldCut_positive {A Q : CompactCarrier.{u}}
    (T : TorusPresentation Q) (he : A = T.cutCarrier) :
    IsOrientedFold (C := A) (fun x : A.Carrier => T.cutMap (he ▸ x)) := by
  cases he
  exact T.isOrientedFold_cutMap

private theorem doubleFoldLeft_smooth (C D N : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    (T : TorusPresentation N) (hcut : T.cutCarrier = C.withBoundarySum D hC hD) :
    ContMDiff C.model N.model ∞ (fun x : C.Carrier => T.cutMap (hcut.symm ▸ Sum.inl x)) :=
  (doubleFoldCut_smooth T hcut.symm).comp (doubleFoldInl_smooth C D hC hD)

private theorem doubleFoldRight_smooth (C D N : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    (T : TorusPresentation N) (hcut : T.cutCarrier = C.withBoundarySum D hC hD) :
    ContMDiff D.model N.model ∞ (fun x : D.Carrier => T.cutMap (hcut.symm ▸ Sum.inr x)) :=
  (doubleFoldCut_smooth T hcut.symm).comp (doubleFoldInr_smooth C D hC hD)

private theorem doubleFoldLeft_positive (C D N : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    (T : TorusPresentation N) (hcut : T.cutCarrier = C.withBoundarySum D hC hD) :
    IsOrientedFold (fun x : C.Carrier => T.cutMap (hcut.symm ▸ Sum.inl x)) :=
  doubleBoundaryFold_comp_positive (doubleFoldCut_smooth T hcut.symm)
    (doubleFoldInl_smooth C D hC hD) (doubleFoldCut_positive T hcut.symm)
    (fun x => ⟨(C.withBoundarySumInlTangentEquiv D hC hD x).toLinearEquiv,
      fun v => C.withBoundarySumInlTangentEquiv_apply D hC hD x v,
      C.withBoundarySumInl_positive D hC hD x⟩)

private theorem doubleFoldRight_positive (C D N : CompactCarrier.{u})
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    (T : TorusPresentation N) (hcut : T.cutCarrier = C.withBoundarySum D hC hD) :
    IsOrientedFold (fun x : D.Carrier => T.cutMap (hcut.symm ▸ Sum.inr x)) :=
  doubleBoundaryFold_comp_positive (doubleFoldCut_smooth T hcut.symm)
    (doubleFoldInr_smooth C D hC hD) (doubleFoldCut_positive T hcut.symm)
    (fun x => ⟨(C.withBoundarySumInrTangentEquiv D hC hD x).toLinearEquiv,
      fun v => C.withBoundarySumInrTangentEquiv_apply D hC hD x v,
      C.withBoundarySumInr_positive D hC hD x⟩)

variable (K0 W K1 N : CompactCarrier.{u}) {Q : CompactCarrier.{u}}
  (hK0 : K0.kind = .withBoundary) (hW : W.kind = .withBoundary)
  (hK1 : K1.kind = .withBoundary) (hN : N.kind = .withBoundary)
  (T1 : TorusPresentation N) (hcut1 : T1.cutCarrier = K0.withBoundarySum W hK0 hW)
  (T2 : TorusPresentation Q) (hcut2 : T2.cutCarrier = N.withBoundarySum K1 hN hK1)

def doubleBoundaryLeftMap (x : K0.Carrier) : Q.Carrier :=
  T2.cutMap (hcut2.symm ▸ Sum.inl (T1.cutMap (hcut1.symm ▸ Sum.inl x)))

def doubleBoundaryMiddleMap (x : W.Carrier) : Q.Carrier :=
  T2.cutMap (hcut2.symm ▸ Sum.inl (T1.cutMap (hcut1.symm ▸ Sum.inr x)))

def doubleBoundaryRightMap (x : K1.Carrier) : Q.Carrier :=
  T2.cutMap (hcut2.symm ▸ Sum.inr x)

local notation "LeftFold" => doubleBoundaryLeftMap K0 W K1 N hK0 hW hK1 hN T1 hcut1 T2 hcut2
local notation "MiddleFold" => doubleBoundaryMiddleMap K0 W K1 N hK0 hW hK1 hN T1 hcut1 T2 hcut2
local notation "RightFold" => doubleBoundaryRightMap K1 N hK1 hN T2 hcut2

theorem doubleBoundaryLeftMap_smooth : ContMDiff K0.model Q.model ∞ LeftFold :=
  (doubleFoldLeft_smooth N K1 Q hN hK1 T2 hcut2).comp
    (doubleFoldLeft_smooth K0 W N hK0 hW T1 hcut1)

theorem doubleBoundaryMiddleMap_smooth : ContMDiff W.model Q.model ∞ MiddleFold :=
  (doubleFoldLeft_smooth N K1 Q hN hK1 T2 hcut2).comp
    (doubleFoldRight_smooth K0 W N hK0 hW T1 hcut1)

theorem doubleBoundaryRightMap_smooth : ContMDiff K1.model Q.model ∞ RightFold :=
  doubleFoldRight_smooth N K1 Q hN hK1 T2 hcut2

theorem doubleBoundaryLeftMap_positive : IsOrientedFold LeftFold :=
  doubleBoundaryFold_comp_positive (A := K0) (B := N) (C := Q)
    (doubleFoldLeft_smooth N K1 Q hN hK1 T2 hcut2)
    (doubleFoldLeft_smooth K0 W N hK0 hW T1 hcut1)
    (doubleFoldLeft_positive N K1 Q hN hK1 T2 hcut2)
    (doubleFoldLeft_positive K0 W N hK0 hW T1 hcut1)

theorem doubleBoundaryMiddleMap_positive : IsOrientedFold MiddleFold :=
  doubleBoundaryFold_comp_positive (A := W) (B := N) (C := Q)
    (doubleFoldLeft_smooth N K1 Q hN hK1 T2 hcut2)
    (doubleFoldRight_smooth K0 W N hK0 hW T1 hcut1)
    (doubleFoldLeft_positive N K1 Q hN hK1 T2 hcut2)
    (doubleFoldRight_positive K0 W N hK0 hW T1 hcut1)

theorem doubleBoundaryRightMap_positive : IsOrientedFold RightFold :=
  doubleFoldRight_positive N K1 Q hN hK1 T2 hcut2

end GC.GraphManifold
