import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgery
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMerge
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplit
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LinearSeams
import DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization

/-!
An actual pants product filled along its fibre has two retained boundary tori and a distinguished
linear split seam. The attaching map is a new physical gluing, with native product markings.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold GC.GraphManifold.TorusPairing
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private def plugSwapUnit : GL (Fin 2) ℤ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def plugMatching : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  linearTorusDiffeomorph plugSwapUnit

private theorem plugMatching_apply (t : Torus) : plugMatching t = (t.2, t.1) := by
  change linearTorusMap !![0, 1; 1, 0] t = _
  simp [linearTorusMap]

private abbrev plugCone : ConeFilling := Merge.sectionFilling 0

private def plugRightMatched :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) ConeFilling.FilledCut.{u} ∞ :=
  let d := plugMatching.prodCongr
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)
  d.toPartialDiffeomorph.trans ConeFilling.rightCollar

private theorem plugRightMatched_source : plugRightMatched.{u}.source = halfCollarSource := by
  ext p
  change (p ∈ univ ∧ (plugMatching p.1, p.2) ∈ ConeFilling.rightCollar.source) ↔ _
  rw [ConeFilling.rightCollar_source]
  simp only [mem_univ, true_and]
  rfl

private theorem collarPullback_orientation {C : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hc : c.source = halfCollarSource)
    (O : ManifoldOrientation halfCollarModel surgeryHalfDomain 3)
    (hO : ∀ p, Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv c
      (hc.symm ▸ (show p.val ∈ halfCollarSource from p.property)))
      (O.orientation p) = C.orientation.orientation (c p.val))
    (p : surgeryHalfDomain) :
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv c
      (hc.symm ▸ (show p.val ∈ halfCollarSource from p.property))).symm
      (C.orientation.orientation (c p.val)) = O.orientation p := by
  rw [← hO p]
  exact (Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv c
    (hc.symm ▸ (show p.val ∈ halfCollarSource from p.property)))).symm_apply_apply _

private theorem collarReversing_of_base {C : CompactCarrier.{u}}
    (l r : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hl : l.source = halfCollarSource) (hr : r.source = halfCollarSource)
    (h0 : Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv l (hl.symm ▸ zero_mem_halfCollarSource torusBase)).symm
      (C.orientation.orientation (l (torusBase, halfZero))) =
      -Orientation.map (Fin 3)
        (carrierSurgeryPatchTangentEquiv r (hr.symm ▸ zero_mem_halfCollarSource torusBase)).symm
        (C.orientation.orientation (r (torusBase, halfZero)))) :
    ReversesBoundaryOrientation C l r := by
  obtain ⟨OL, hOL⟩ := exists_surgeryHalfCollarOrientation l hl
  obtain ⟨OR, hOR⟩ := exists_surgeryHalfCollarOrientation r hr
  let p0 : surgeryHalfDomain := ⟨(torusBase, halfZero), zero_mem_halfCollarSource torusBase⟩
  have he0 : OL.orientation p0 = OR.opposite.orientation p0 := by
    change OL.orientation p0 = -OR.orientation p0
    rw [← collarPullback_orientation l hl OL hOL p0,
      ← collarPullback_orientation r hr OR hOR p0]
    exact h0
  have he : OL = OR.opposite := OL.eq_of_eq_at OR.opposite p0 he0
  intro t
  let p : surgeryHalfDomain := ⟨(t, halfZero), zero_mem_halfCollarSource t⟩
  let L := carrierSurgeryPatchTangentEquiv l
    (hl.symm ▸ (show p.val ∈ halfCollarSource from p.property))
  let R := carrierSurgeryPatchTangentEquiv r
    (hr.symm ▸ (show p.val ∈ halfCollarSource from p.property))
  refine ⟨L, R, fun v => rfl, fun v => rfl, ?_⟩
  exact (collarPullback_orientation l hl OL hOL p).trans
    ((congrArg (fun O : ManifoldOrientation halfCollarModel surgeryHalfDomain 3 =>
      O.orientation p) he).trans
      (congrArg Neg.neg (collarPullback_orientation r hr OR hOR p).symm))

private def plugSolidOrientation : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3 :=
  solidAtlas.orientation planeCircleOrientation

private def plugCutCarrier (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3) :
    CompactCarrier.{u} :=
  { kind := .withBoundary
    Carrier := ConeFilling.FilledCut.{u}
    charts := inferInstance
    smooth := inferInstance
    orientation := ManifoldOrientation.sum (productCarrier 3 (Or.inr rfl)).orientation O }

private abbrev plugComponents (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3) :
    (plugCutCarrier O).Components where
  count := 2
  count_pos := plugCone.filledComponents.{u}.count_pos
  piece := plugCone.filledComponents.{u}.piece
  closed := plugCone.filledComponents.{u}.closed
  connected := plugCone.filledComponents.{u}.connected
  disjoint := plugCone.filledComponents.{u}.disjoint
  covers := plugCone.filledComponents.{u}.covers
  interior_connected := plugCone.filledComponents.{u}.interior_connected

private def plugExternal (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3) :
    BoundaryTori (plugCutCarrier O) 2 where
  collar := plugCone.cutExternal.collar
  source_eq := plugCone.cutExternal.source_eq
  boundary_zero := plugCone.cutExternal.boundary_zero
  disjoint := plugCone.cutExternal.disjoint

private theorem exists_plugCutOrientation :
    ∃ O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3,
      ReversesBoundaryOrientation (plugCutCarrier O) plugCone.leftCollar plugRightMatched := by
  let C := plugCutCarrier plugSolidOrientation
  let p := (torusBase, halfZero)
  let L := carrierSurgeryPatchTangentEquiv plugCone.leftCollar
    (plugCone.leftCollar_source.symm ▸ zero_mem_halfCollarSource torusBase)
  let R := carrierSurgeryPatchTangentEquiv plugRightMatched
    (plugRightMatched_source.symm ▸ zero_mem_halfCollarSource torusBase)
  let a := Orientation.map (Fin 3) L.symm (C.orientation.orientation (plugCone.leftCollar p))
  let b := -Orientation.map (Fin 3) R.symm (C.orientation.orientation (plugRightMatched p))
  rcases a.eq_or_eq_neg b (by
    change 3 = Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
    simp) with h | h
  · refine ⟨plugSolidOrientation, collarReversing_of_base
      (C := plugCutCarrier plugSolidOrientation)
      plugCone.leftCollar plugRightMatched plugCone.leftCollar_source plugRightMatched_source h⟩
  · refine ⟨plugSolidOrientation.opposite, collarReversing_of_base
      (C := plugCutCarrier plugSolidOrientation.opposite)
      plugCone.leftCollar plugRightMatched plugCone.leftCollar_source plugRightMatched_source ?_⟩
    let o : Orientation ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3) :=
      C.orientation.orientation (plugCone.leftCollar p)
    change Orientation.map (Fin 3) L.symm (-o) = b
    calc
      Orientation.map (Fin 3) L.symm (-o) = -a := Orientation.map_neg L.symm o
      _ = b := (congrArg Neg.neg h).trans (neg_neg b)

private def plugGluing : BoundaryGluing ConeFilling.FilledCut.{u} (Fin 1) :=
  { plugCone.gluing with
    attaching := Function.const (Fin 1) (plugCone.leftParam.symm.trans
      (plugMatching.toHomeomorph.trans ConeFilling.rightParam)) }

private def plugPairing (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3)
    (hO : ReversesBoundaryOrientation (plugCutCarrier O) plugCone.leftCollar
      plugRightMatched) : TorusPairing (plugCutCarrier O) where
  count := 1
  gluing := plugGluing
  leftParam j := plugCone.leftParam
  rightParam j := ConeFilling.rightParam
  matching j := plugMatching
  matching_eq j t := by
    change (plugCone.leftParam.symm.trans
      (plugMatching.toHomeomorph.trans ConeFilling.rightParam)) (plugCone.leftParam t) = _
    simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rfl
  leftCollar j := plugCone.leftCollar
  rightCollar j := ConeFilling.rightCollar
  left_source j := plugCone.leftCollar_source
  right_source j := ConeFilling.rightCollar_source
  left_zero j t := rfl
  right_zero j t := rfl
  reversing j := hO

private theorem plugBoundary (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3)
    (hO : ReversesBoundaryOrientation (plugCutCarrier O) plugCone.leftCollar
      plugRightMatched) :
    (plugCutCarrier O).model.boundary (plugCutCarrier O).Carrier =
      (⋃ j, (plugPairing O hO).gluing.block j) ∪ plugCone.cutExternal.image :=
  plugCone.cut_boundary

private theorem plugBoundary_disjoint (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3)
    (hO : ReversesBoundaryOrientation (plugCutCarrier O) plugCone.leftCollar
      plugRightMatched) :
    Disjoint (⋃ j, (plugPairing O hO).gluing.block j) plugCone.cutExternal.image :=
  plugCone.filledPresentation.external_disjoint

private theorem plugLeft_owned (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3)
    (hO : ReversesBoundaryOrientation (plugCutCarrier O) plugCone.leftCollar
      plugRightMatched) (j : Fin 1) :
    (plugPairing O hO).gluing.left j ⊆
      (plugCone.filledComponents.{u}.piece 1 : Set ConeFilling.FilledCut) :=
  plugCone.filledPresentation.left_owned j

private theorem plugRight_owned (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3)
    (hO : ReversesBoundaryOrientation (plugCutCarrier O) plugCone.leftCollar
      plugRightMatched) (j : Fin 1) :
    (plugPairing O hO).gluing.right j ⊆
      (plugCone.filledComponents.{u}.piece 0 : Set ConeFilling.FilledCut) :=
  plugCone.filledPresentation.right_owned j

private theorem plugExternal_owned (j : Fin 2) :
    range (plugCone.cutExternal.torusMap j) ⊆
      (plugCone.filledComponents.{u}.piece 0 : Set ConeFilling.FilledCut) :=
  plugCone.filledPresentation.external_owned j

private abbrev plugShrunkPairing (OC : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3)
    (hOC : ReversesBoundaryOrientation (plugCutCarrier OC) plugCone.leftCollar
      plugRightMatched) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :=
  (plugPairing OC hOC).shrink hδ hδ1

section

variable (OC : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3)
  (hOC : ReversesBoundaryOrientation (plugCutCarrier OC) plugCone.leftCollar plugRightMatched)
  {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)


variable [A : ChartedSpace CarrierModel.withBoundary.Space ((plugShrunkPairing OC hOC hδ
  hδ1)).QuotientSpace]
  [hman : IsManifold CarrierModel.withBoundary.model ∞ ((plugShrunkPairing OC hOC hδ
    hδ1)).QuotientSpace]
  (hs : Pairwise fun i j => Disjoint (((plugShrunkPairing OC hOC hδ hδ1)).surgerySideCollar
    i).target
    (((plugShrunkPairing OC hOC hδ hδ1)).surgerySideCollar j).target)
  (hex : ∀ i j, Disjoint ((((plugExternal OC).shrink hδ hδ1)).collar i).target
    (((plugShrunkPairing OC hOC hδ hδ1)).surgerySideCollar j).target)
  (hpatch : ∀ i, ContMDiffOn (((plugShrunkPairing OC hOC hδ hδ1)).surgeryPatchModel 2 i) (𝓡∂ 3) ∞
      (((plugShrunkPairing OC hOC hδ hδ1)).surgeryPatch (plugComponents OC) ((plugExternal
        OC).shrink hδ hδ1) hs hex ((plugPairing OC hOC).surgeryShrink_boundary (plugExternal OC)
        hδ hδ1 (plugBoundary OC hOC)) i) (((plugShrunkPairing OC hOC hδ hδ1)).surgeryPatch
        (plugComponents OC) ((plugExternal OC).shrink hδ hδ1) hs hex ((plugPairing OC
        hOC).surgeryShrink_boundary (plugExternal OC) hδ hδ1 (plugBoundary OC hOC)) i).source ∧
    ContMDiffOn (𝓡∂ 3) (((plugShrunkPairing OC hOC hδ hδ1)).surgeryPatchModel 2 i) ∞
      (((plugShrunkPairing OC hOC hδ hδ1)).surgeryPatch (plugComponents OC) ((plugExternal
        OC).shrink hδ hδ1) hs hex ((plugPairing OC hOC).surgeryShrink_boundary (plugExternal OC)
        hδ hδ1 (plugBoundary OC hOC)) i).symm
      (((plugShrunkPairing OC hOC hδ hδ1)).surgeryPatch (plugComponents OC) ((plugExternal
        OC).shrink hδ hδ1) hs hex ((plugPairing OC hOC).surgeryShrink_boundary (plugExternal OC)
        hδ hδ1 (plugBoundary OC hOC)) i).target)
  (O : ManifoldOrientation (𝓡∂ 3) ((plugShrunkPairing OC hOC hδ hδ1)).QuotientSpace 3)
  (ho : ∀ x : ((plugCutCarrier OC)).Carrier,
    Orientation.map (Fin 3) (((plugShrunkPairing OC hOC hδ hδ1)).surgeryQuotientFoldTangentEquiv
      (k := .withBoundary) (plugComponents OC) ((plugExternal OC).shrink hδ hδ1) hs hex
        ((plugPairing OC hOC).surgeryShrink_boundary (plugExternal OC) hδ hδ1 (plugBoundary OC
        hOC)) hpatch x)
      (((plugCutCarrier OC)).orientation.orientation x) = O.orientation (((plugShrunkPairing OC
        hOC hδ hδ1)).quotientMap x))

private def plugTorus : TorusPresentation (((plugShrunkPairing OC hOC hδ hδ1)).surgeryCarrier (k
  := .withBoundary) O) :=
  ((plugShrunkPairing OC hOC hδ hδ1)).surgeryPresentation (k := .withBoundary) (plugComponents OC)
    ((plugExternal OC).shrink hδ hδ1) hs hex ((plugPairing OC hOC).surgeryShrink_boundary
    (plugExternal OC) hδ hδ1 (plugBoundary OC hOC)) hpatch O ho
    (Function.const (Fin ((plugShrunkPairing OC hOC hδ hδ1)).count) 1) (Function.const (Fin
      ((plugShrunkPairing OC hOC hδ hδ1)).count) 0)
    (Function.const (Fin 2) 0) (plugLeft_owned OC hOC) (plugRight_owned OC hOC)
    (TorusPairing.surgeryShrink_external_owned (plugExternal OC) hδ hδ1 (plugComponents OC)
      (Function.const (Fin 2) 0) plugExternal_owned)


private def plugHostPortFun (j : Fin 3) : ((plugTorus OC hOC hδ hδ1 hs hex hpatch O ho)).OwnedSide
  ⟨0, by change 0 < 2; decide⟩ :=
  ![⟨.inr (.inr (0 : Fin 2)), rfl⟩, ⟨.inr (.inl (0 : Fin 1)), rfl⟩,
    ⟨.inr (.inr (1 : Fin 2)), rfl⟩] j

private def plugHostPortInv : ((plugTorus OC hOC hδ hδ1 hs hex hpatch O ho)).OwnedSide ⟨0, by
  change 0 < 2; decide⟩ → Fin 3
  | ⟨.inl _, _⟩ => 1
  | ⟨.inr (.inl _), _⟩ => 1
  | ⟨.inr (.inr e), _⟩ => ConeFilling.externalPort e

private def plugHostPort : Fin 3 ≃ ((plugTorus OC hOC hδ hδ1 hs hex hpatch O ho)).OwnedSide ⟨0, by
  change 0 < 2; decide⟩ where
  toFun := plugHostPortFun OC hOC hδ hδ1 hs hex hpatch O ho
  invFun := plugHostPortInv OC hOC hδ hδ1 hs hex hpatch O ho
  left_inv j := by
    rcases ConeFilling.fin_three_cases j with rfl | rfl | rfl <;> rfl
  right_inv s := by
    rcases s with ⟨m | m | e, h⟩
    · change (1 : Fin 2) = 0 at h
      exact absurd h (by decide)
    · change Fin 1 at m
      obtain rfl : m = 0 := Subsingleton.elim m 0
      rfl
    · rcases ConeFilling.fin_two_cases e with rfl | rfl <;> rfl

private def plugSolidPort : Fin 1 ≃ ((plugTorus OC hOC hδ hδ1 hs hex hpatch O ho)).OwnedSide ⟨1,
  by change 1 < 2; decide⟩ where
  toFun j := ⟨.inl (0 : Fin 1), rfl⟩
  invFun s := 0
  left_inv j := Subsingleton.elim _ _
  right_inv s := by
    rcases s with ⟨m | m | e, h⟩
    · change Fin 1 at m
      obtain rfl : m = 0 := Subsingleton.elim m 0
      rfl
    · change (0 : Fin 2) = 1 at h
      exact absurd h (by decide)
    · change (0 : Fin 2) = 1 at h
      exact absurd h (by decide)

private def plugHost : ProductFibredPiece (plugTorus OC hOC hδ hδ1 hs hex hpatch O ho) ⟨0, by
  change 0 < 2; decide⟩ 3 where
  base := pantsPlanarBase.shrink hδ hδ1
  port := plugHostPort OC hOC hδ hδ1 hs hex hpatch O ho
  trivialization := ConeFilling.productTrivialization
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
    rcases ConeFilling.fin_three_cases j with rfl | rfl | rfl <;> rfl

private def plugSolid : ProductFibredPiece (plugTorus OC hOC hδ hδ1 hs hex hpatch O ho) ⟨1, by
  change 1 < 2; decide⟩ 1 where
  base := (discPlanarBase 1).shrink hδ hδ1
  port := plugSolidPort OC hOC hδ hδ1 hs hex hpatch O ho
  trivialization := ConeFilling.solidTrivialization
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp, Subsingleton.elim j 0]
    rfl

private def plugElementary : ElementaryPresentation (((plugShrunkPairing OC hOC hδ
  hδ1)).surgeryCarrier (k := .withBoundary) O) :=
  { toTorus := (plugTorus OC hOC hδ hδ1 hs hex hpatch O ho)
    kind := ![3, 1]
    kind_mem := by
      intro i
      fin_cases i
      · change (3 : ℕ) ∈ ({1, 2, 3} : Finset ℕ)
        decide
      · change (1 : ℕ) ∈ ({1, 2, 3} : Finset ℕ)
        decide
    piece := (show (i : Fin 2) → ProductFibredPiece (plugTorus OC hOC hδ hδ1 hs hex hpatch O ho) i
      (![3, 1] i) from
      Fin.cases (plugHost OC hOC hδ hδ1 hs hex hpatch O ho) (fun j => by
        obtain rfl := Subsingleton.elim j 0
        exact plugSolid OC hOC hδ hδ1 hs hex hpatch O ho)) }

end

theorem exists_fibrePlug :
    ∃ (W : CompactCarrier.{u}) (E : ElementaryPresentation W)
      (j : Fin E.toTorus.pairing.count),
      W.kind = .withBoundary ∧ E.toTorus.components.count = 2 ∧
      E.toTorus.pairing.count = 1 ∧ E.toTorus.externalCount = 2 ∧
      E.IsSplitSeam j true ∧ E.IsLinearSeam j := by
  obtain ⟨OC, hOC⟩ := exists_plugCutOrientation.{u}
  let C := plugCutCarrier OC
  let D : C.Components := plugComponents OC
  let P := plugPairing OC hOC
  let E0 : BoundaryTori C 2 := plugExternal OC
  obtain ⟨δ, hδ, hδ1, hs, hex⟩ :=
    P.exists_surgeryCommonShrink E0 (plugBoundary_disjoint OC hOC)
  let S := P.shrink hδ hδ1
  let E1 := (E0).shrink hδ hδ1
  have hb := P.surgeryShrink_boundary E0 hδ hδ1 (plugBoundary OC hOC)
  obtain ⟨A, hman, hpatch⟩ := S.exists_surgeryHalfQuotientAtlas D E1 hs hex hb
  let := A
  let := hman
  obtain ⟨O, ho⟩ := S.exists_surgeryQuotientOrientation (k := .withBoundary)
    D E1 hs hex hb hpatch (fun j => S.surgerySignedOrientation hs j)
    (fun j x hx => S.surgerySignedOrientation_map hs j (x := x) hx)
  let W := S.surgeryCarrier (k := .withBoundary) O
  let E := plugElementary OC hOC hδ hδ1 hs hex hpatch O ho
  refine ⟨W, E, ⟨0, by change 0 < 1; decide⟩, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · refine ⟨rfl, rfl, ?_⟩
    change PrimitiveSlope.delta (torusUnit plugMatching • meridianSlope) fiberSlope = 0
    rw [plugMatching, torusUnit_linearTorusDiffeomorph]
    change (slopeDet (smulVec !![0, 1; 1, 0] (1, 0)) (0, 1)).natAbs = 0
    norm_num [smulVec, slopeDet]
  · change plugMatching = linearTorusDiffeomorph (torusUnit plugMatching)
    rw [plugMatching, torusUnit_linearTorusDiffeomorph]

end GC.GraphManifold
