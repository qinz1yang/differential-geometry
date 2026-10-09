import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryPortPairing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgery
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CliffordBlocks

/-!
A second-circle reflection in an actual solid boundary marking corrects physical port orientation.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold.TorusPairing
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold


def boundaryPortSecondReflection : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (Diffeomorph.refl (𝓡 1) Circle ∞).prodCongr circleInvDiffeo

theorem boundaryPortSecondReflection_apply (t : Torus) :
    boundaryPortSecondReflection t = (t.1, t.2⁻¹) := rfl

def boundaryPortMarkedReflection (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (ψ.symm.trans boundaryPortSecondReflection).trans ψ

theorem boundaryPortMarkedReflection_apply
    (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (t : Torus) :
    boundaryPortMarkedReflection ψ t = ψ ((ψ.symm t).1, (ψ.symm t).2⁻¹) := rfl

theorem boundaryPortMarkedReflection_meridian
    (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (s : Circle) :
    boundaryPortMarkedReflection ψ (ψ (s, 1)) = ψ (s, 1) := by
  rw [boundaryPortMarkedReflection_apply, ψ.symm_apply_apply, inv_one]


def boundaryPortSolidReflection :
    solidTorusSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidTorusSet.{u} :=
  (solidTorusDiscCircle.trans
    ((Diffeomorph.refl (𝓡∂ 2) UnitDisc.{u} ∞).prodCongr circleInvDiffeo)).trans
      solidTorusDiscCircle.symm

theorem boundaryPortSolidReflection_collar (p : Torus × EuclideanHalfSpace 1) :
    boundaryPortSolidReflection.{u} (solidTorusCollar p) =
      solidTorusCollar (boundaryPortSecondReflection p.1, p.2) := by
  rcases p with ⟨⟨s, t⟩, r⟩
  rw [solidTorusCollar_eq_symm]
  change solidTorusDiscCircle.symm
    ((Diffeomorph.refl (𝓡∂ 2) UnitDisc.{u} ∞).prodCongr circleInvDiffeo
      (solidTorusDiscCircle (solidTorusDiscCircle.symm (cliffordDiscCollarMap (s, r), t)))) = _
  rw [solidTorusDiscCircle.apply_symm_apply]
  exact (solidTorusCollar_eq_symm s t⁻¹ r).symm

theorem boundaryPortSolidReflection_marked_collar
    (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (p : Torus × EuclideanHalfSpace 1) :
    boundaryPortSolidReflection.{u} (solidTorusCollar (ψ.symm p.1, p.2)) =
      solidTorusCollar (ψ.symm (boundaryPortMarkedReflection ψ p.1), p.2) := by
  rw [boundaryPortSolidReflection_collar]
  change solidTorusCollar (boundaryPortSecondReflection (ψ.symm p.1), p.2) =
    solidTorusCollar (ψ.symm (ψ (boundaryPortSecondReflection (ψ.symm p.1))), p.2)
  rw [ψ.symm_apply_apply]

private def boundaryPortHalfAction (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    surgeryHalfDomain ≃ₘ⟮halfCollarModel, halfCollarModel⟯ surgeryHalfDomain where
  toEquiv :=
    { toFun p := ⟨(f p.val.1, p.val.2), p.property⟩
      invFun p := ⟨(f.symm p.val.1, p.val.2), p.property⟩
      left_inv p := by apply Subtype.ext; exact Prod.ext (f.symm_apply_apply p.val.1) rfl
      right_inv p := by apply Subtype.ext; exact Prod.ext (f.apply_symm_apply p.val.1) rfl }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff surgeryHalfDomain _).mp
    exact (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).contMDiff.comp
      contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff surgeryHalfDomain _).mp
    exact (f.symm.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).contMDiff.comp
      contMDiff_subtype_val

private theorem boundaryPortHalfAction_derivative
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (p : surgeryHalfDomain) :
    mfderiv halfCollarModel halfCollarModel (boundaryPortHalfAction f) p =
      mfderiv halfCollarModel halfCollarModel
        (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)) p.val := by
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp (boundaryPortHalfAction f)]
  exact DifferentialGeometry.mfderiv_restrict_open
    (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)) surgeryHalfDomain p

set_option backward.isDefEq.respectTransparency false in
private theorem boundaryPortHalfReflection_negative
    (O : ManifoldOrientation halfCollarModel surgeryHalfDomain 3) :
    (boundaryPortHalfAction boundaryPortSecondReflection).preservesOrientation O O.opposite := by
  let p : surgeryHalfDomain := ⟨(torusBase, halfZero), zero_mem_halfCollarSource torusBase⟩
  have hfix : boundaryPortHalfAction boundaryPortSecondReflection p = p := by
    apply Subtype.ext
    change ((torusBase.1, torusBase.2⁻¹), halfZero) = (torusBase, halfZero)
    exact Prod.ext (Prod.ext rfl inv_one) rfl
  apply Diffeomorph.preservesOrientation_of_eq_at
    (boundaryPortHalfAction boundaryPortSecondReflection) O O.opposite p
  rw [hfix]
  let L := ((boundaryPortHalfAction boundaryPortSecondReflection).mfderivToContinuousLinearEquiv
    (by simp) p).toLinearEquiv
  have he : L.toLinearMap =
      ((LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] _).prodMap
        (-LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] _)).prodMap
          (LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] _) := by
    ext v
    change mfderiv halfCollarModel halfCollarModel
      (boundaryPortHalfAction boundaryPortSecondReflection) p v = _
    rw [boundaryPortHalfAction_derivative]
    change mfderiv halfCollarModel halfCollarModel
      (Prod.map (Prod.map id circleInvDiffeo) id) (torusBase, halfZero) v = _
    erw [mfderiv_prodMap
      (boundaryPortSecondReflection.contMDiff.mdifferentiableAt (by simp)) mdifferentiableAt_id,
      mfderiv_prodMap mdifferentiableAt_id (circleInvDiffeo.contMDiff.mdifferentiableAt (by simp)),
      mfderiv_id, mfderiv_id]
    change ((v.1.1, mfderiv (𝓡 1) (𝓡 1) circleInvDiffeo 1 v.1.2), v.2) = _
    erw [mfderiv_circleInv_apply]
    rfl
  have hd : LinearMap.det L.toLinearMap < 0 := by
    erw [he, LinearMap.det_prodMap, LinearMap.det_prodMap,
      show (-LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] _) =
        (-1 : ℝ) • LinearMap.id by ext v; simp, LinearMap.det_smul]
    simp only [LinearMap.det_id]
    norm_num
  exact (Orientation.map_eq_neg_iff_det_neg (O.orientation p) L (by
    change 3 = Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
    simp)).mpr hd

private theorem boundaryPortHalfAction_trans
    (f g : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    boundaryPortHalfAction (f.trans g) =
      (boundaryPortHalfAction f).trans (boundaryPortHalfAction g) := by
  apply Diffeomorph.ext
  intro p
  rfl

private theorem boundaryPortHalfAction_symm
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    boundaryPortHalfAction f.symm = (boundaryPortHalfAction f).symm := by
  apply Diffeomorph.ext
  intro p
  rfl

private theorem boundaryPortHalfConjugate_negative
    (a R : surgeryHalfDomain ≃ₘ⟮halfCollarModel, halfCollarModel⟯ surgeryHalfDomain)
    (hR : ∀ O : ManifoldOrientation halfCollarModel surgeryHalfDomain 3,
      R.preservesOrientation O O.opposite)
    (O : ManifoldOrientation halfCollarModel surgeryHalfDomain 3) :
    ((a.symm.trans R).trans a).preservesOrientation O O.opposite := by
  rcases preservesOrientation_or_opposite a O O with ha | ha
  · exact Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_trans (Diffeomorph.preservesOrientation_symm ha) (hR O))
      (Diffeomorph.preservesOrientation_opposite ha)
  · have hR' : R.preservesOrientation O.opposite O := by
      simpa only [ManifoldOrientation.opposite_opposite] using hR O.opposite
    have ha' : a.preservesOrientation O O.opposite := by
      simpa only [ManifoldOrientation.opposite_opposite] using
        Diffeomorph.preservesOrientation_opposite ha
    exact Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_trans (Diffeomorph.preservesOrientation_symm ha) hR') ha'

private theorem boundaryPortHalfMarked_negative
    (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (O : ManifoldOrientation halfCollarModel surgeryHalfDomain 3) :
    (boundaryPortHalfAction (boundaryPortMarkedReflection ψ)).preservesOrientation
      O O.opposite := by
  unfold boundaryPortMarkedReflection
  rw [boundaryPortHalfAction_trans, boundaryPortHalfAction_trans, boundaryPortHalfAction_symm]
  exact boundaryPortHalfConjugate_negative (boundaryPortHalfAction ψ)
    (boundaryPortHalfAction boundaryPortSecondReflection) boundaryPortHalfReflection_negative O

private def boundaryPortMatchedCollar {S : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel S.model
      (Torus × EuclideanHalfSpace 1) S.Carrier ∞)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    PartialDiffeomorph halfCollarModel S.model
      (Torus × EuclideanHalfSpace 1) S.Carrier ∞ :=
  (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans c

private theorem boundaryPortMatchedCollar_source {S : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel S.model
      (Torus × EuclideanHalfSpace 1) S.Carrier ∞)
    (hc : c.source = halfCollarSource)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (boundaryPortMatchedCollar c f).source = halfCollarSource := by
  ext p
  change (p ∈ univ ∧ (f p.1, p.2) ∈ c.source) ↔ p ∈ halfCollarSource
  rw [hc]
  simp only [mem_univ, true_and]
  rfl

private theorem boundaryPortPullback {S : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel S.model
      (Torus × EuclideanHalfSpace 1) S.Carrier ∞)
    (hc : c.source = halfCollarSource)
    (O : ManifoldOrientation halfCollarModel surgeryHalfDomain 3)
    (hO : ∀ p, Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv c
      (hc.symm ▸ (show p.val ∈ halfCollarSource from p.property)))
      (O.orientation p) = S.orientation.orientation (c p.val)) (p : surgeryHalfDomain) :
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv c
      (hc.symm ▸ (show p.val ∈ halfCollarSource from p.property))).symm
      (S.orientation.orientation (c p.val)) = O.orientation p := by
  rw [← hO p]
  exact (Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv c
    (hc.symm ▸ (show p.val ∈ halfCollarSource from p.property)))).symm_apply_apply _

private theorem boundaryPortOpposite_reversing {S : CompactCarrier.{u}}
    (l r : PartialDiffeomorph halfCollarModel S.model
      (Torus × EuclideanHalfSpace 1) S.Carrier ∞)
    (hl : l.source = halfCollarSource) (hr : r.source = halfCollarSource)
    (OL OR : ManifoldOrientation halfCollarModel surgeryHalfDomain 3)
    (hOL : ∀ p, Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv l
      (hl.symm ▸ (show p.val ∈ halfCollarSource from p.property)))
      (OL.orientation p) = S.orientation.orientation (l p.val))
    (hOR : ∀ p, Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv r
      (hr.symm ▸ (show p.val ∈ halfCollarSource from p.property)))
      (OR.orientation p) = S.orientation.orientation (r p.val))
    (he : OL = OR.opposite) : ReversesBoundaryOrientation S l r := by
  intro t
  let p : surgeryHalfDomain := ⟨(t, halfZero), zero_mem_halfCollarSource t⟩
  let L := carrierSurgeryPatchTangentEquiv l
    (hl.symm ▸ (show p.val ∈ halfCollarSource from p.property))
  let R := carrierSurgeryPatchTangentEquiv r
    (hr.symm ▸ (show p.val ∈ halfCollarSource from p.property))
  refine ⟨L, R, fun v => rfl, fun v => rfl, ?_⟩
  change Orientation.map (Fin 3) L.symm (S.orientation.orientation (l p.val)) =
    -Orientation.map (Fin 3) R.symm (S.orientation.orientation (r p.val))
  rw [boundaryPortPullback l hl OL hOL p, boundaryPortPullback r hr OR hOR p, he]
  rfl

private theorem boundaryPortNegative_map {E F H : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup H] [Module ℝ H]
    (A : E ≃ₗ[ℝ] F) (R : F ≃ₗ[ℝ] H)
    (o : Orientation ℝ E (Fin 3)) (b : Orientation ℝ F (Fin 3))
    (c : Orientation ℝ H (Fin 3))
    (hR : Orientation.map (Fin 3) R.symm c = b)
    (hA : Orientation.map (Fin 3) A o = -b) :
    o = -Orientation.map (Fin 3) (A.trans R).symm c := by
  have hi : Orientation.map (Fin 3) A.symm b = -o := by
    apply (Orientation.map (Fin 3) A).injective
    rw [← Orientation.map_symm (Fin 3) A, Equiv.apply_symm_apply, Orientation.map_neg, hA]
    exact (neg_neg b).symm
  rw [LinearEquiv.trans_symm, DifferentialGeometry.orientation_map_trans, hR, hi]
  exact (neg_neg o).symm

set_option backward.isDefEq.respectTransparency false in
private theorem exists_boundaryPortCollarMatching {S : CompactCarrier.{u}}
    (l r : PartialDiffeomorph halfCollarModel S.model
      (Torus × EuclideanHalfSpace 1) S.Carrier ∞)
    (hl : l.source = halfCollarSource) (hr : r.source = halfCollarSource)
    (f0 ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    ∃ ε : Bool, ReversesBoundaryOrientation S l
      (fun p => r ((f0.trans (if ε then boundaryPortMarkedReflection ψ
        else Diffeomorph.refl torusModel Torus ∞)) p.1, p.2)) := by
  let r0 := boundaryPortMatchedCollar r f0
  have hr0 : r0.source = halfCollarSource := boundaryPortMatchedCollar_source r hr f0
  obtain ⟨OL, hOL⟩ := exists_surgeryHalfCollarOrientation l hl
  obtain ⟨OR, hOR⟩ := exists_surgeryHalfCollarOrientation r0 hr0
  let p0 : surgeryHalfDomain := ⟨(torusBase, halfZero), zero_mem_halfCollarSource torusBase⟩
  have hdim : Fintype.card (Fin 3) = Module.finrank ℝ (TangentSpace halfCollarModel p0) := by
    change 3 = Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
    simp
  rcases (OL.orientation p0).eq_or_eq_neg (OR.orientation p0) hdim with he | he
  · have hsame : OL = OR := OL.eq_of_eq_at OR p0 he
    let Rψ := boundaryPortMarkedReflection ψ
    let k := (f0.trans Rψ).trans f0.symm
    let a := boundaryPortHalfAction k
    have ha : a.preservesOrientation OR OR.opposite := by
      change (boundaryPortHalfAction ((f0.trans Rψ).trans f0.symm)).preservesOrientation OR _
      rw [boundaryPortHalfAction_trans, boundaryPortHalfAction_trans]
      have hs : boundaryPortHalfAction f0 = (boundaryPortHalfAction f0.symm).symm := by
        rw [boundaryPortHalfAction_symm]
        rfl
      rw [hs]
      exact boundaryPortHalfConjugate_negative (boundaryPortHalfAction f0.symm)
        (boundaryPortHalfAction Rψ) (boundaryPortHalfMarked_negative ψ) OR
    let r1 := boundaryPortMatchedCollar r (f0.trans Rψ)
    let K := k.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)
    have hf : (r1 : Torus × EuclideanHalfSpace 1 → S.Carrier) = r0 ∘ K := by
      funext p
      change r (Rψ (f0 p.1), p.2) = r (f0 (f0.symm (Rψ (f0 p.1))), p.2)
      rw [f0.apply_symm_apply]
    refine ⟨true, ?_⟩
    change ReversesBoundaryOrientation S l r1
    intro t
    let p : surgeryHalfDomain := ⟨(t, halfZero), zero_mem_halfCollarSource t⟩
    let q := a p
    let L := carrierSurgeryPatchTangentEquiv l
      (hl.symm ▸ (show p.val ∈ halfCollarSource from p.property))
    let R := carrierSurgeryPatchTangentEquiv r0
      (hr0.symm ▸ (show q.val ∈ halfCollarSource from q.property))
    let A := (a.mfderivToContinuousLinearEquiv (by simp) p).toLinearEquiv
    refine ⟨L, A.trans R, fun v => rfl, ?_, ?_⟩
    · intro v
      change mfderiv halfCollarModel S.model r0 q.val
        (mfderiv halfCollarModel halfCollarModel a p v) =
          mfderiv halfCollarModel S.model r1 p.val v
      rw [boundaryPortHalfAction_derivative, hf]
      exact (mfderiv_comp_apply p.val
        (r0.mdifferentiableAt (by simp) (hr0.symm ▸
          (show q.val ∈ halfCollarSource from q.property)))
        (K.contMDiff.mdifferentiableAt (by simp)) v).symm
    · have hpoint : r1 p.val = r0 q.val := congrFun hf p.val
      change Orientation.map (Fin 3) L.symm (S.orientation.orientation (l p.val)) =
        -Orientation.map (Fin 3) (A.trans R).symm (S.orientation.orientation (r1 p.val))
      have hLo : Orientation.map (Fin 3) L.symm
          (S.orientation.orientation (l p.val)) = OR.orientation p := by
        exact (boundaryPortPullback l hl OL hOL p).trans
          (congrArg (fun o : ManifoldOrientation halfCollarModel surgeryHalfDomain 3 =>
            o.orientation p) hsame)
      have hRo : Orientation.map (Fin 3) R.symm
          (S.orientation.orientation (r0 q.val)) = OR.orientation q :=
        boundaryPortPullback r0 hr0 OR hOR q
      have hn : Orientation.map (Fin 3) A (OR.orientation p) = -OR.orientation q := ha p
      exact hLo.trans ((boundaryPortNegative_map A R (OR.orientation p) (OR.orientation q)
        (S.orientation.orientation (r0 q.val)) hRo hn).trans
          (congrArg (fun x => -Orientation.map (Fin 3) (A.trans R).symm
            (S.orientation.orientation x)) hpoint.symm))
  · have hopp : OL = OR.opposite := OL.eq_of_eq_at OR.opposite p0 he
    refine ⟨false, ?_⟩
    change ReversesBoundaryOrientation S l r0
    exact boundaryPortOpposite_reversing l r0 hl hr0 OL OR hOL hOR hopp


theorem exists_boundaryPortReversingMatching
    (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    [Nonempty C.Carrier] [Nonempty D.Carrier]
    {n : ℕ} (E1 : BoundaryTori C 1) (E2 : BoundaryTori D (n + 1))
    (f0 ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    ∃ ε : Bool, ReversesBoundaryOrientation (withBoundarySum C D hC hD)
      (boundaryPortLeftCollar C D hC hD E1)
      (fun p => boundaryPortRightCollar C D hC hD E2 0
        ((f0.trans (if ε then boundaryPortMarkedReflection ψ
          else Diffeomorph.refl torusModel Torus ∞)) p.1, p.2)) :=
  exists_boundaryPortCollarMatching
    (boundaryPortLeftCollar C D hC hD E1) (boundaryPortRightCollar C D hC hD E2 0)
    (boundaryPortLeftCollar_source C D hC hD E1)
    (boundaryPortRightCollar_source C D hC hD E2 0) f0 ψ

end GC.GraphManifold
