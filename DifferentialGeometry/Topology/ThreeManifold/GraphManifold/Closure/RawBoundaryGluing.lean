import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryPortPairing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierSum
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.LocalRawFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgery

/-!
Actual one-port boundary gluing of oriented bounded carriers, with its residual port and raw
presentation obtained from the genuine component identifications and local face assembly.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
  [ConnectedSpace C.Carrier] [ConnectedSpace D.Carrier]

def rawBoundarySumComponents : (C.withBoundarySum D hC hD).Components :=
  C.withBoundarySumComponents D hC hD
    (singleComponents C (connectedSpace_pieceInterior_top C))
    (singleComponents D (connectedSpace_pieceInterior_top D))

def rawBoundaryLeftIndex : Fin (rawBoundarySumComponents C D hC hD).count :=
  finSumFinEquiv (.inl (0 : Fin 1))

def rawBoundaryRightIndex : Fin (rawBoundarySumComponents C D hC hD).count :=
  finSumFinEquiv (.inr (0 : Fin 1))

theorem rawBoundarySumComponents_count : (rawBoundarySumComponents C D hC hD).count = 2 := rfl

theorem rawBoundarySumComponents_left :
    ((rawBoundarySumComponents C D hC hD).piece (rawBoundaryLeftIndex C D hC hD) :
      Set (C.withBoundarySum D hC hD).Carrier) = range Sum.inl := by
  exact (C.withBoundarySumComponents_piece_left D hC hD
    (singleComponents C (connectedSpace_pieceInterior_top C))
    (singleComponents D (connectedSpace_pieceInterior_top D)) ⟨0, Nat.one_pos⟩).trans image_univ

theorem rawBoundarySumComponents_right :
    ((rawBoundarySumComponents C D hC hD).piece (rawBoundaryRightIndex C D hC hD) :
      Set (C.withBoundarySum D hC hD).Carrier) = range Sum.inr := by
  exact (C.withBoundarySumComponents_piece_right D hC hD
    (singleComponents C (connectedSpace_pieceInterior_top C))
    (singleComponents D (connectedSpace_pieceInterior_top D)) ⟨0, Nat.one_pos⟩).trans image_univ

private def rawBoundaryOpenDiffeomorph {A S : CompactCarrier.{u}}
    (e : PartialDiffeomorph A.model S.model A.Carrier S.Carrier ∞)
    (U : Opens S.Carrier) (hs : e.source = univ) (ht : e.target = U) :
    A.Carrier ≃ₘ⟮A.model, S.model⟯ U where
  toFun x := ⟨e x, ht.subset (e.map_source (hs.symm.subset (mem_univ x)))⟩
  invFun y := e.symm y.val
  left_inv x := e.left_inv (hs.symm.subset (mem_univ x))
  right_inv y := Subtype.ext (e.right_inv (ht.symm.subset y.property))
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    apply contMDiffOn_univ.mp
    change ContMDiffOn A.model S.model ∞ e univ
    rw [← hs]
    exact e.contMDiffOn
  contMDiff_invFun := e.symm.contMDiffOn.comp_contMDiff contMDiff_subtype_val
    (fun y => ht.symm.subset y.property)

private theorem rawBoundaryOpenDiffeomorph_mfderiv {A S : CompactCarrier.{u}}
    (e : PartialDiffeomorph A.model S.model A.Carrier S.Carrier ∞)
    (U : Opens S.Carrier) (hs : e.source = univ) (ht : e.target = U) (x : A.Carrier) :
    mfderiv A.model S.model (rawBoundaryOpenDiffeomorph e U hs ht) x =
      mfderiv A.model S.model e x := by
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp
    (rawBoundaryOpenDiffeomorph e U hs ht) x]
  rfl

def rawBoundaryLeftDiffeomorph :
    C.Carrier ≃ₘ⟮C.model,
      (GC.Topology.componentCarrier (C.withBoundarySum D hC hD) (rawBoundarySumComponents C D hC hD)
        (rawBoundaryLeftIndex C D hC hD)).model⟯
      (GC.Topology.componentCarrier (C.withBoundarySum D hC hD) (rawBoundarySumComponents C D hC hD)
        (rawBoundaryLeftIndex C D hC hD)).Carrier :=
  rawBoundaryOpenDiffeomorph (C.withBoundarySumLeft D hC hD)
    ((rawBoundarySumComponents C D hC hD).piece (rawBoundaryLeftIndex C D hC hD))
    (C.withBoundarySumLeft_source D hC hD)
    ((C.withBoundarySumLeft_target D hC hD).trans
      (rawBoundarySumComponents_left C D hC hD).symm)

def rawBoundaryRightDiffeomorph :
    D.Carrier ≃ₘ⟮D.model,
      (GC.Topology.componentCarrier (C.withBoundarySum D hC hD) (rawBoundarySumComponents C D hC hD)
        (rawBoundaryRightIndex C D hC hD)).model⟯
      (GC.Topology.componentCarrier (C.withBoundarySum D hC hD) (rawBoundarySumComponents C D hC hD)
        (rawBoundaryRightIndex C D hC hD)).Carrier :=
  rawBoundaryOpenDiffeomorph (C.withBoundarySumRight D hC hD)
    ((rawBoundarySumComponents C D hC hD).piece (rawBoundaryRightIndex C D hC hD))
    (C.withBoundarySumRight_source D hC hD)
    ((C.withBoundarySumRight_target D hC hD).trans
      (rawBoundarySumComponents_right C D hC hD).symm)

theorem rawBoundaryLeftDiffeomorph_apply (x : C.Carrier) :
    (rawBoundaryLeftDiffeomorph C D hC hD x).val = (Sum.inl x : C.Carrier ⊕ D.Carrier) :=
  C.withBoundarySumLeft_apply D hC hD x

theorem rawBoundaryRightDiffeomorph_apply (x : D.Carrier) :
    (rawBoundaryRightDiffeomorph C D hC hD x).val = (Sum.inr x : C.Carrier ⊕ D.Carrier) :=
  C.withBoundarySumRight_apply D hC hD x

set_option backward.isDefEq.respectTransparency false in
theorem rawBoundaryLeftDiffeomorph_positive :
    (rawBoundaryLeftDiffeomorph C D hC hD).preservesOrientation C.orientation
      (GC.Topology.componentCarrier (C.withBoundarySum D hC hD) (rawBoundarySumComponents C D hC hD)
        (rawBoundaryLeftIndex C D hC hD)).orientation := by
  intro x
  have he : ((rawBoundaryLeftDiffeomorph C D hC hD).mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv =
      (C.withBoundarySumInlTangentEquiv D hC hD x).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv C.model (C.withBoundarySum D hC hD).model
      (rawBoundaryOpenDiffeomorph (C.withBoundarySumLeft D hC hD) _
        (C.withBoundarySumLeft_source D hC hD) _) x v = _
    rw [rawBoundaryOpenDiffeomorph_mfderiv]
    have hf : (C.withBoundarySumLeft D hC hD).toFun = Sum.inl :=
      funext (C.withBoundarySumLeft_apply D hC hD)
    change mfderiv C.model (C.withBoundarySum D hC hD).model
      (C.withBoundarySumLeft D hC hD).toFun x v = _
    rw [hf]
    rfl
  rw [he]
  change Orientation.map (Fin 3) (C.withBoundarySumInlTangentEquiv D hC hD x).toLinearEquiv
    (C.orientation.orientation x) =
      (C.withBoundarySum D hC hD).orientation.orientation
        (rawBoundaryLeftDiffeomorph C D hC hD x).val
  rw [rawBoundaryLeftDiffeomorph_apply]
  exact C.withBoundarySumInl_positive D hC hD x

set_option backward.isDefEq.respectTransparency false in
theorem rawBoundaryRightDiffeomorph_positive :
    (rawBoundaryRightDiffeomorph C D hC hD).preservesOrientation D.orientation
      (GC.Topology.componentCarrier (C.withBoundarySum D hC hD) (rawBoundarySumComponents C D hC hD)
        (rawBoundaryRightIndex C D hC hD)).orientation := by
  intro x
  have he : ((rawBoundaryRightDiffeomorph C D hC hD).mfderivToContinuousLinearEquiv
      (by simp) x).toLinearEquiv =
      (C.withBoundarySumInrTangentEquiv D hC hD x).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv D.model (C.withBoundarySum D hC hD).model
      (rawBoundaryOpenDiffeomorph (C.withBoundarySumRight D hC hD) _
        (C.withBoundarySumRight_source D hC hD) _) x v = _
    rw [rawBoundaryOpenDiffeomorph_mfderiv]
    have hf : (C.withBoundarySumRight D hC hD).toFun = Sum.inr :=
      funext (C.withBoundarySumRight_apply D hC hD)
    change mfderiv D.model (C.withBoundarySum D hC hD).model
      (C.withBoundarySumRight D hC hD).toFun x v = _
    rw [hf]
    rfl
  rw [he]
  change Orientation.map (Fin 3) (C.withBoundarySumInrTangentEquiv D hC hD x).toLinearEquiv
    (D.orientation.orientation x) =
      (C.withBoundarySum D hC hD).orientation.orientation
        (rawBoundaryRightDiffeomorph C D hC hD x).val
  rw [rawBoundaryRightDiffeomorph_apply]
  exact C.withBoundarySumInr_positive D hC hD x

variable {n : ℕ} (E1 : BoundaryTori C 1) (E2 : BoundaryTori D (n + 1))
  (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  (hrev : ReversesBoundaryOrientation (C.withBoundarySum D hC hD)
    (boundaryPortLeftCollar C D hC hD E1)
    (fun p => boundaryPortRightCollar C D hC hD E2 0 (f p.1, p.2)))

theorem rawBoundaryQuotient_connected :
    ConnectedSpace (boundaryPortPairing C D hC hD E1 E2 f hrev).QuotientSpace := by
  let P := boundaryPortPairing C D hC hD E1 E2 f hrev
  let l : C.Carrier → P.QuotientSpace := fun x => P.quotientMap (Sum.inl x)
  let r : D.Carrier → P.QuotientSpace := fun x => P.quotientMap (Sum.inr x)
  have hl : Continuous l := P.quotientMap.continuous.comp continuous_inl
  have hr : Continuous r := P.quotientMap.continuous.comp continuous_inr
  have he : P.quotientMap (P.leftParam ⟨0, Nat.one_pos⟩ 1).val =
      P.quotientMap (P.rightParam ⟨0, Nat.one_pos⟩ (f 1)).val := by
    apply Quotient.sound
    have h := P.gluing.rel_of_mem_left (P.leftParam ⟨0, Nat.one_pos⟩ 1).property
    rw [P.matching_eq] at h
    exact h
  change l (E1.torusMap 0 1) = r (E2.torusMap 0 (f 1)) at he
  have hmeet : (range l ∩ range r).Nonempty :=
    ⟨l (E1.torusMap 0 1), mem_range_self _, ⟨E2.torusMap 0 (f 1), he.symm⟩⟩
  have hcover : range l ∪ range r = univ := by
    apply eq_univ_of_forall
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    cases x with
    | inl x => exact Or.inl (mem_range_self x)
    | inr x => exact Or.inr (mem_range_self x)
  apply connectedSpace_iff_univ.mpr
  rw [← hcover]
  exact (isConnected_range hl).union hmeet (isConnected_range hr)

theorem rawBoundaryPairing_left_owned :
    ∀ j, (boundaryPortPairing C D hC hD E1 E2 f hrev).gluing.left j ⊆
      (rawBoundarySumComponents C D hC hD).piece (rawBoundaryLeftIndex C D hC hD) := by
  intro j x hx
  have hx' : ∃ t, Sum.inl (E1.torusMap 0 t) = x := hx
  rw [rawBoundarySumComponents_left]
  obtain ⟨t, rfl⟩ := hx'
  exact mem_range_self _

theorem rawBoundaryPairing_right_owned :
    ∀ j, (boundaryPortPairing C D hC hD E1 E2 f hrev).gluing.right j ⊆
      (rawBoundarySumComponents C D hC hD).piece (rawBoundaryRightIndex C D hC hD) := by
  intro j x hx
  have hx' : ∃ t, Sum.inr (E2.torusMap 0 t) = x := hx
  rw [rawBoundarySumComponents_right]
  obtain ⟨t, rfl⟩ := hx'
  exact mem_range_self _

omit E1 f hrev in
theorem rawBoundaryRemaining_owned :
    ∀ i, range ((boundaryPortRemaining C D hC hD E2).torusMap i) ⊆
      (rawBoundarySumComponents C D hC hD).piece (rawBoundaryRightIndex C D hC hD) := by
  intro i x hx
  obtain ⟨t, rfl⟩ := hx
  rw [rawBoundarySumComponents_right]
  exact ⟨E2.torusMap i.succ t, (boundaryPortRemaining_torusMap C D hC hD E2 i t).symm⟩

set_option backward.isDefEq.respectTransparency false in
theorem exists_rawBoundaryTorusPresentation
    (hbC : C.model.boundary C.Carrier = E1.image)
    (hbD : D.model.boundary D.Carrier = E2.image) :
    ∃ N : CompactCarrier.{u},
      N.kind = .withBoundary ∧
      ConnectedSpace N.Carrier ∧ ∃ T : TorusPresentation N,
        ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ hδ1 : δ ≤ 1,
          ∃ hcut : T.cutCarrier = C.withBoundarySum D hC hD,
            ∃ hn : T.externalCount = n, ∃ hc : T.components.count = 2,
              (hcut ▸ T.components) = rawBoundarySumComponents C D hC hD ∧
              (hcut ▸ T.pairing) = (boundaryPortPairing C D hC hD E1 E2 f hrev).shrink hδ hδ1 ∧
              (hcut ▸ (hn ▸ T.cutExternal)) = (boundaryPortRemaining C D hC hD E2).shrink hδ hδ1 ∧
              T.pairing.count = 1 ∧ (∀ j, T.pairing.matching j = f) ∧
              (∀ j, (T.leftPiece j).val = 0 ∧ (T.rightPiece j).val = 1) ∧
              (∀ i, (T.externalPiece i).val = 1) ∧
              ∃ eC : C.Carrier ≃ₘ⟮C.model, (T.Component (Fin.cast hc.symm 0)).model⟯
                  (T.Component (Fin.cast hc.symm 0)).Carrier,
                ∃ eD : D.Carrier ≃ₘ⟮D.model, (T.Component (Fin.cast hc.symm 1)).model⟯
                    (T.Component (Fin.cast hc.symm 1)).Carrier,
                  eC.preservesOrientation C.orientation
                    (T.Component (Fin.cast hc.symm 0)).orientation ∧
                  eD.preservesOrientation D.orientation
                    (T.Component (Fin.cast hc.symm 1)).orientation ∧
                  ∃ e : (boundaryPortPairing C D hC hD E1 E2 f hrev).QuotientSpace ≃ₜ N.Carrier,
                    (∀ x, e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap x) =
                      T.cutMap (hcut.symm ▸ x)) ∧
                    (∀ i p, p ∈ halfCollarSource →
                      T.external.collar (Fin.cast hn.symm i) p =
                        e ((boundaryPortPairing C D hC hD E1 E2 f hrev).quotientMap
                          (Sum.inr (E2.collar i.succ (p.1, halfSpaceScale hδ p.2))))) := by
  let P := boundaryPortPairing C D hC hD E1 E2 f hrev
  let E := boundaryPortRemaining C D hC hD E2
  let DS := rawBoundarySumComponents C D hC hD
  let := rawBoundaryQuotient_connected C D hC hD E1 E2 f hrev
  have hb := boundaryPortPairing_boundary C D hC hD E1 E2 f hrev hbC hbD
  have hd := boundaryPortPairing_external_disjoint C D hC hD E1 E2 f hrev
  obtain ⟨δ, hδ, hδ1, hs, hex⟩ := P.exists_surgeryCommonShrink E hd
  let S := P.shrink hδ hδ1
  let F := E.shrink hδ hδ1
  have hbS := P.surgeryShrink_boundary E hδ hδ1 hb
  obtain ⟨A, hman, hpatch⟩ := S.exists_surgeryHalfQuotientAtlas DS F hs hex hbS
  let := A
  let := hman
  obtain ⟨O, ho⟩ := S.exists_surgeryQuotientOrientation (k := .withBoundary) DS F hs hex hbS hpatch
    (fun j => S.surgerySignedOrientation hs j)
    (fun j x hx => S.surgerySignedOrientation_map hs j (x := x) hx)
  let N := S.surgeryCarrier (k := .withBoundary) O
  let T : TorusPresentation N := S.surgeryPresentation DS F hs hex hbS hpatch O ho
    (Function.const (Fin S.count) (rawBoundaryLeftIndex C D hC hD))
    (Function.const (Fin S.count) (rawBoundaryRightIndex C D hC hD))
    (Function.const (Fin n) (rawBoundaryRightIndex C D hC hD))
    (rawBoundaryPairing_left_owned C D hC hD E1 E2 f hrev)
    (rawBoundaryPairing_right_owned C D hC hD E1 E2 f hrev)
    (TorusPairing.surgeryShrink_external_owned E hδ hδ1 DS
      (Function.const (Fin n) (rawBoundaryRightIndex C D hC hD))
      (rawBoundaryRemaining_owned C D hC hD E2))
  refine ⟨N, rfl, rawBoundaryQuotient_connected C D hC hD E1 E2 f hrev, T, δ, hδ, hδ1,
    rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, fun j => rfl, fun j => ⟨rfl, rfl⟩, fun i => rfl,
    rawBoundaryLeftDiffeomorph C D hC hD, rawBoundaryRightDiffeomorph C D hC hD,
    rawBoundaryLeftDiffeomorph_positive C D hC hD,
    rawBoundaryRightDiffeomorph_positive C D hC hD, Homeomorph.refl P.QuotientSpace,
    fun x => rfl, ?_⟩
  intro i p hp
  have h := T.marked_collar i p hp
  change P.quotientMap ((E.shrink hδ hδ1).collar i p) = T.external.collar i p at h
  rw [BoundaryTori.shrink_collar_apply, boundaryPortRemaining_apply] at h
  exact h.symm

include hC hD hrev in
set_option backward.isDefEq.respectTransparency false in
theorem exists_rawBoundaryGluing
    (hbC : C.model.boundary C.Carrier = E1.image)
    (hbD : D.model.boundary D.Carrier = E2.image)
    (GC : RawGraphPresentation C) (GD : RawGraphPresentation D) :
    ∃ N : CompactCarrier.{u}, N.kind = .withBoundary ∧ ConnectedSpace N.Carrier ∧
      ∃ G : RawGraphPresentation N, G.externalCount = n ∧
        ∃ j : Fin G.pairing.count, G.pairing.matching j = f := by
  obtain ⟨N, hN, hconn, T, δ, hδ, hδ1, hcut, hn, hc, hcomponents, hpairing,
    hexternal, hcount, hmatching, howners, hexowner, eC, eD, hposC, hposD, e, hsquare, hport⟩ :=
    exists_rawBoundaryTorusPresentation C D hC hD E1 E2 f hrev hbC hbD
  have hR : ∀ i : Fin T.components.count, Nonempty (RawGraphPresentation (T.Component i)) := by
    intro i
    have hi : i.val < 2 := hc ▸ i.isLt
    have hcases : i = Fin.cast hc.symm 0 ∨ i = Fin.cast hc.symm 1 := by
      by_cases hi0 : i.val = 0
      · exact Or.inl (Fin.ext hi0)
      · exact Or.inr (Fin.ext (by change i.val = 1; omega))
    rcases hcases with rfl | rfl
    · exact ⟨GC.transport eC hposC⟩
    · exact ⟨GD.transport eD hposD⟩
  let R : ∀ i, RawGraphPresentation (T.Component i) := fun i => Classical.choice (hR i)
  obtain ⟨port, ψ, Φ, hΦ, ε, hε, hε1, hzero, hgerm, hfull, G, hG, edge,
    hmarked, hold, hnew, hmatch, hmatchnew⟩ := exists_rawFacesAssembly T R
  let j : Fin T.pairing.count := ⟨0, by rw [hcount]; exact Nat.one_pos⟩
  exact ⟨N, hN, hconn, G, hG.trans hn, edge (.inl j),
    (hmatch j).trans (hmatching j)⟩

end GC.GraphManifold
