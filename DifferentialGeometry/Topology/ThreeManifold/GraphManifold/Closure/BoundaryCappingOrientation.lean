import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryCappingCommutation
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgerySeamOrientation

/-!
Actual relative sphere capping preserves the induced torus collar orientations and physical gluing.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold.TorusPairing
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

set_option backward.isDefEq.respectTransparency false in
private theorem cappingCollarPullback_comp {C Q : CompactCarrier.{u}}
    (l : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (r : PartialDiffeomorph halfCollarModel Q.model
      (Torus × EuclideanHalfSpace 1) Q.Carrier ∞)
    (hl : l.source = halfCollarSource) (hr : r.source = halfCollarSource)
    (f : C.Carrier → Q.Carrier) (hf : ContMDiff C.model Q.model ∞ f)
    (he : ∀ p ∈ halfCollarSource, r p = f (l p))
    (p0 : surgeryHalfDomain)
    (hpos : ∃ A : TangentSpace C.model (l p0.val) ≃ₗ[ℝ]
        TangentSpace Q.model (f (l p0.val)),
      (∀ v, A v = mfderiv C.model Q.model f (l p0.val) v) ∧
        Orientation.map (Fin 3) A (C.orientation.orientation (l p0.val)) =
          Q.orientation.orientation (f (l p0.val))) :
    ∀ p (hp : p ∈ halfCollarSource),
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv l (hl.symm ▸ hp)).symm
        (C.orientation.orientation (l p)) =
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv r (hr.symm ▸ hp)).symm
        (Q.orientation.orientation (r p)) := by
  obtain ⟨OL, hOL⟩ := exists_surgeryHalfCollarOrientation l hl
  obtain ⟨OR, hOR⟩ := exists_surgeryHalfCollarOrientation r hr
  obtain ⟨A, hA, hAo⟩ := hpos
  let L := carrierSurgeryPatchTangentEquiv l
    (hl.symm ▸ (show p0.val ∈ halfCollarSource from p0.property))
  let R := carrierSurgeryPatchTangentEquiv r
    (hr.symm ▸ (show p0.val ∈ halfCollarSource from p0.property))
  have hder : R = L.trans A := by
    apply LinearEquiv.ext
    intro v
    have hg : (r : Torus × EuclideanHalfSpace 1 → Q.Carrier) =ᶠ[𝓝 p0.val] f ∘ l := by
      filter_upwards [surgeryHalfDomain.isOpen.mem_nhds p0.property] with p hp
      exact he p hp
    change mfderiv halfCollarModel Q.model r p0.val v = A (L v)
    rw [hg.mfderiv_eq]
    change mfderiv halfCollarModel Q.model (f ∘ l) p0.val v = A (L v)
    rw [mfderiv_comp_apply p0.val (hf.mdifferentiableAt (by simp))
      (l.mdifferentiableAt (by simp)
        (hl.symm ▸ (show p0.val ∈ halfCollarSource from p0.property))), ← hA]
    rfl
  have hpoint : OL.orientation p0 = OR.orientation p0 := by
    apply (Orientation.map (Fin 3) R).injective
    rw [hder, DifferentialGeometry.orientation_map_trans, hOL]
    have hR0 := hOR p0
    change Orientation.map (Fin 3) R (OR.orientation p0) = _ at hR0
    rw [hder] at hR0
    apply hAo.trans
    calc
      Q.orientation.orientation (f (l p0.val)) = Q.orientation.orientation (r p0.val) := by
        rw [he p0.val p0.property]
      _ = _ := hR0.symm
  have hsame : OL = OR := OL.eq_of_eq_at OR p0 hpoint
  intro p hp
  let q : surgeryHalfDomain := ⟨p, hp⟩
  have hL := hOL q
  have hR := hOR q
  rw [← hL, ← hR, hsame]
  exact (Orientation.map (Fin 3)
    (carrierSurgeryPatchTangentEquiv l (hl.symm ▸ hp))).symm_apply_apply
    (OR.orientation q) |>.trans
      ((Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv r
        (hr.symm ▸ hp))).symm_apply_apply (OR.orientation q)).symm

private def cappingMatchedCollar {C : CompactCarrier.{u}}
    (l : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞ :=
  (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans l

private theorem cappingMatchedCollar_source {C : CompactCarrier.{u}}
    (l : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞) (hl : l.source = halfCollarSource)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (cappingMatchedCollar l f).source = halfCollarSource := by
  ext p
  change (p ∈ univ ∧ (f p.1, p.2) ∈ l.source) ↔ p ∈ halfCollarSource
  rw [hl]
  simp only [mem_univ, true_and]
  rfl

private def cappingHalfPoint : surgeryHalfDomain :=
  ⟨(torusBase, halfPoint (1 / 2) (by norm_num)), by
    change (1 / 2 : ℝ) < 1
    norm_num⟩

private theorem cappingHalfPoint_interior : halfCollarModel.IsInteriorPoint cappingHalfPoint.val :=
  halfCollarModel_isInteriorPoint' (by change (0 : ℝ) < 1 / 2; norm_num)

private theorem cappingSumLeft_pullback
    (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    [Nonempty C.Carrier]
    (l : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞) (hl : l.source = halfCollarSource)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv l (hl.symm ▸ hp)).symm
      (C.orientation.orientation (l p)) =
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv
      (l.trans (withBoundarySumLeft C D hC hD)) (by
        change p ∈ l.source ∧ l p ∈ (withBoundarySumLeft C D hC hD).source
        exact ⟨hl.symm ▸ hp, (withBoundarySumLeft_source C D hC hD).symm ▸ mem_univ _⟩)).symm
      ((withBoundarySum C D hC hD).orientation.orientation
        ((l.trans (withBoundarySumLeft C D hC hD)) p)) := by
  have hs : (l.trans (withBoundarySumLeft C D hC hD)).source = halfCollarSource := by
    ext q
    change (q ∈ l.source ∧ l q ∈ (withBoundarySumLeft C D hC hD).source) ↔ _
    rw [hl, withBoundarySumLeft_source]
    simp
  apply cappingCollarPullback_comp l (l.trans (withBoundarySumLeft C D hC hD)) hl hs
    (withBoundarySumLeft C D hC hD) ?_ (fun q hq => rfl) cappingHalfPoint
    (withBoundarySumLeft_positive C D hC hD _) p hp
  rw [← contMDiffOn_univ, ← withBoundarySumLeft_source C D hC hD]
  exact (withBoundarySumLeft C D hC hD).contMDiffOn

private theorem cappingSumRight_pullback
    (C D : CompactCarrier.{u}) (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    [Nonempty D.Carrier]
    (l : PartialDiffeomorph halfCollarModel D.model
      (Torus × EuclideanHalfSpace 1) D.Carrier ∞) (hl : l.source = halfCollarSource)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv l (hl.symm ▸ hp)).symm
      (D.orientation.orientation (l p)) =
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv
      (l.trans (withBoundarySumRight C D hC hD)) (by
        change p ∈ l.source ∧ l p ∈ (withBoundarySumRight C D hC hD).source
        exact ⟨hl.symm ▸ hp, (withBoundarySumRight_source C D hC hD).symm ▸ mem_univ _⟩)).symm
      ((withBoundarySum C D hC hD).orientation.orientation
        ((l.trans (withBoundarySumRight C D hC hD)) p)) := by
  have hs : (l.trans (withBoundarySumRight C D hC hD)).source = halfCollarSource := by
    ext q
    change (q ∈ l.source ∧ l q ∈ (withBoundarySumRight C D hC hD).source) ↔ _
    rw [hl, withBoundarySumRight_source]
    simp
  apply cappingCollarPullback_comp l (l.trans (withBoundarySumRight C D hC hD)) hl hs
    (withBoundarySumRight C D hC hD) ?_ (fun q hq => rfl) cappingHalfPoint
    (withBoundarySumRight_positive C D hC hD _) p hp
  rw [← contMDiffOn_univ, ← withBoundarySumRight_source C D hC hD]
  exact (withBoundarySumRight C D hC hD).contMDiffOn

set_option backward.isDefEq.respectTransparency false in
private theorem cappingReversing_iff {C : CompactCarrier.{u}}
    {l r : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞}
    (hl : l.source = halfCollarSource) (hr : r.source = halfCollarSource) :
    ReversesBoundaryOrientation C l r ↔ ∀ t : Torus,
      Orientation.map (Fin 3)
        (carrierSurgeryPatchTangentEquiv l (hl.symm ▸ zero_mem_halfCollarSource t)).symm
        (C.orientation.orientation (l (t, halfZero))) =
      -Orientation.map (Fin 3)
        (carrierSurgeryPatchTangentEquiv r (hr.symm ▸ zero_mem_halfCollarSource t)).symm
        (C.orientation.orientation (r (t, halfZero))) := by
  constructor
  · intro h t
    obtain ⟨L, R, hL, hR, hO⟩ := h t
    have heL : L = carrierSurgeryPatchTangentEquiv l
        (hl.symm ▸ zero_mem_halfCollarSource t) := LinearEquiv.ext hL
    have heR : R = carrierSurgeryPatchTangentEquiv r
        (hr.symm ▸ zero_mem_halfCollarSource t) := LinearEquiv.ext hR
    rw [heL, heR] at hO
    exact hO
  · intro h t
    exact ⟨carrierSurgeryPatchTangentEquiv l (hl.symm ▸ zero_mem_halfCollarSource t),
      carrierSurgeryPatchTangentEquiv r (hr.symm ▸ zero_mem_halfCollarSource t),
      fun v => rfl, fun v => rfl, h t⟩

private theorem cappingCastCollar {C : CompactCarrier.{u}} {n m : ℕ}
    (hn : n = m) (E : BoundaryTori C n) (i : Fin m) :
    (hn ▸ E).collar i = E.collar (Fin.cast hn.symm i) := by
  cases hn
  rfl

namespace RelativeSphereCapping

variable {C Q : CompactCarrier.{u}} {B : MixedBoundaryCertificate C}
    (K : RelativeSphereCapping C Q B)

private theorem cappingRetainedMatched_pullback (i : Fin B.torusCount)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv
      (cappingMatchedCollar (B.tori.collar i) f)
      ((cappingMatchedCollar_source _ (B.tori.source_eq i) f).symm ▸ hp)).symm
      (C.orientation.orientation (cappingMatchedCollar (B.tori.collar i) f p)) =
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv
      (cappingMatchedCollar (K.retained.collar i) f)
      ((cappingMatchedCollar_source _ (K.retained.source_eq i) f).symm ▸ hp)).symm
      (Q.orientation.orientation (cappingMatchedCollar (K.retained.collar i) f p)) := by
  let l := cappingMatchedCollar (B.tori.collar i) f
  let r := cappingMatchedCollar (K.retained.collar i) f
  have hl : l.source = halfCollarSource := cappingMatchedCollar_source _ (B.tori.source_eq i) f
  have hr : r.source = halfCollarSource := cappingMatchedCollar_source _ (K.retained.source_eq i) f
  have he : ∀ q ∈ halfCollarSource, r q = K.core (l q) := by
    intro q hq
    exact K.retained_collar i (f q.1, q.2) hq
  have hi : C.model.IsInteriorPoint (l cappingHalfPoint.val) :=
    ((l.isLocalDiffeomorphAt halfCollarModel C.model ∞
      (hl.symm ▸ (show cappingHalfPoint.val ∈ halfCollarSource from
        cappingHalfPoint.property))).isInteriorPoint_iff (by simp)).mp cappingHalfPoint_interior
  obtain ⟨hb, hO⟩ := K.core_positive _ hi
  apply cappingCollarPullback_comp l r hl hr K.core K.core_embedding.contMDiff he
    cappingHalfPoint ?_ p hp
  exact ⟨LinearEquiv.ofBijective (mfderiv C.model Q.model K.core
    (l cappingHalfPoint.val)).toLinearMap hb, fun v => rfl, hO⟩

variable (C1 C2 Q2 : CompactCarrier.{u})
  (hC1 : C1.kind = .withBoundary) (hC2 : C2.kind = .withBoundary)
  (hQ2 : Q2.kind = .withBoundary)
  [Nonempty C1.Carrier] [Nonempty C2.Carrier] [Nonempty Q2.Carrier]
  (B : MixedBoundaryCertificate C2) (ht : B.torusCount = 1)
  (K : RelativeSphereCapping C2 Q2 B) (E1 : BoundaryTori C1 1)
  (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)

set_option backward.isDefEq.respectTransparency false in
theorem boundaryCapping_reverses
    (hrev0 : ReversesBoundaryOrientation (withBoundarySum C1 C2 hC1 hC2)
      (boundaryPortLeftCollar C1 C2 hC1 hC2 E1)
      (fun p => boundaryPortRightCollar C1 C2 hC1 hC2 (boundaryCappingTori C2 B ht) 0
        (f p.1, p.2))) :
    ReversesBoundaryOrientation (withBoundarySum C1 Q2 hC1 hQ2)
      (boundaryPortLeftCollar C1 Q2 hC1 hQ2 E1)
      (fun p => boundaryPortRightCollar C1 Q2 hC1 hQ2
        (boundaryCappingRetained C2 Q2 B ht K) 0 (f p.1, p.2)) := by
  let l := E1.collar 0
  let r0 := cappingMatchedCollar ((boundaryCappingTori C2 B ht).collar 0) f
  let r1 := cappingMatchedCollar ((boundaryCappingRetained C2 Q2 B ht K).collar 0) f
  let L0 := l.trans (withBoundarySumLeft C1 C2 hC1 hC2)
  let L1 := l.trans (withBoundarySumLeft C1 Q2 hC1 hQ2)
  let R0 := r0.trans (withBoundarySumRight C1 C2 hC1 hC2)
  let R1 := r1.trans (withBoundarySumRight C1 Q2 hC1 hQ2)
  have hl : l.source = halfCollarSource := E1.source_eq 0
  have hr0 : r0.source = halfCollarSource :=
    cappingMatchedCollar_source _ ((boundaryCappingTori C2 B ht).source_eq 0) f
  have hr1 : r1.source = halfCollarSource :=
    cappingMatchedCollar_source _ ((boundaryCappingRetained C2 Q2 B ht K).source_eq 0) f
  have hL0 : L0.source = halfCollarSource :=
    boundaryPortLeftCollar_source C1 C2 hC1 hC2 E1
  have hL1 : L1.source = halfCollarSource :=
    boundaryPortLeftCollar_source C1 Q2 hC1 hQ2 E1
  have hR0 : R0.source = halfCollarSource := by
    ext p
    change (p ∈ r0.source ∧ r0 p ∈ (withBoundarySumRight C1 C2 hC1 hC2).source) ↔ _
    rw [hr0, withBoundarySumRight_source]
    simp
  have hR1 : R1.source = halfCollarSource := by
    ext p
    change (p ∈ r1.source ∧ r1 p ∈ (withBoundarySumRight C1 Q2 hC1 hQ2).source) ↔ _
    rw [hr1, withBoundarySumRight_source]
    simp
  have hold : ReversesBoundaryOrientation (withBoundarySum C1 C2 hC1 hC2) L0 R0 := hrev0
  change ReversesBoundaryOrientation (withBoundarySum C1 Q2 hC1 hQ2) L1 R1
  apply (cappingReversing_iff (l := L1) (r := R1) hL1 hR1).mpr
  intro t
  have hp := zero_mem_halfCollarSource t
  have hleft0 := cappingSumLeft_pullback C1 C2 hC1 hC2 l hl (t, halfZero) hp
  have hleft1 := cappingSumLeft_pullback C1 Q2 hC1 hQ2 l hl (t, halfZero) hp
  have hright0 := cappingSumRight_pullback C1 C2 hC1 hC2 r0 hr0 (t, halfZero) hp
  have hright1 := cappingSumRight_pullback C1 Q2 hC1 hQ2 r1 hr1 (t, halfZero) hp
  have hcore := cappingRetainedMatched_pullback K (Fin.cast ht.symm 0) f (t, halfZero) hp
  have he0 : (boundaryCappingTori C2 B ht).collar 0 = B.tori.collar (Fin.cast ht.symm 0) :=
    cappingCastCollar ht B.tori 0
  have he1 : (boundaryCappingRetained C2 Q2 B ht K).collar 0 =
      K.retained.collar (Fin.cast ht.symm 0) := cappingCastCollar ht K.retained 0
  have hc : Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv r0 (hr0.symm ▸ hp)).symm
      (C2.orientation.orientation (r0 (t, halfZero))) =
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv r1 (hr1.symm ▸ hp)).symm
        (Q2.orientation.orientation (r1 (t, halfZero))) := by
    dsimp only [r0, r1]
    convert hcore using 1
    · simp only [he0]
      congr 1
      congr 1
      exact congrArg (fun q => q (f t, halfZero)) he0
    · simp only [he1]
      congr 1
      congr 1
      exact congrArg (fun q => q (f t, halfZero)) he1
  have h := (cappingReversing_iff (l := L0) (r := R0) hL0 hR0).mp hold t
  exact hleft1.symm.trans (hleft0.trans (h.trans
    (congrArg Neg.neg (hright0.symm.trans (hc.trans hright1)))))


def boundaryCappingCorePuncture_of_reverses
    (hrev0 : ReversesBoundaryOrientation (withBoundarySum C1 C2 hC1 hC2)
      (boundaryPortLeftCollar C1 C2 hC1 hC2 E1)
      (fun p => boundaryPortRightCollar C1 C2 hC1 hC2 (boundaryCappingTori C2 B ht) 0
        (f p.1, p.2))) :
    (boundaryCappingUncappedPairing C1 C2 hC1 hC2 B ht E1 f hrev0).QuotientSpace ≃ₜ
      ↥(boundaryCappingOpenCaps C1 C2 Q2 hC1 hQ2 B ht K E1 f
        (boundaryCapping_reverses C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0))ᶜ :=
  boundaryCappingCorePunctureHomeomorph C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0
    (boundaryCapping_reverses C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0)


end RelativeSphereCapping
end GC.GraphManifold
