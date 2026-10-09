import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminalSelfSeam
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockCharts
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Sigma
import Mathlib.Topology.Homeomorph.Quotient
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanNormal

/-!
# Charts for a single distance one filling

A selected star which exhausts its presentation gives a block on the same carrier.
The actual filling quotient identifies only its selected seam. The other sides retain their
full external collars. Both seam directions give one normal filling of a pants with two ports;
linear matching gives charts directly, and general matching uses TorusMappingClassLinear.
Full carrier comparisons descend standardizations of the cut pieces, with matching checked
on a small signed collar at each glued seam. The two inner holes use the section-filling model;
the outer port uses its full geometric capping model and its signed radial chart. All three
ports give a whole annulus times circle diffeomorphism. External collars need no prescribed image.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.SelectedStarGroup

variable {W : CompactCarrier.{u}} {T : TorusPresentation W} {d : SeifertData}
  (G : SelectedStarGroup T d)
  (hcover : ∀ i, i ∈ G.set) (hseams : ∀ k, k ∈ G.selected)

def wholePiece : Option (Fin d.fillingCount) → Fin T.components.count
  | none => G.center
  | some l => T.leftPiece (G.arm l)

include hcover in
theorem wholePiece_bijective : Function.Bijective G.wholePiece := by
  constructor
  · rintro (_ | l) (_ | l') he
    · rfl
    · exact absurd he (G.solid_ne_center l').symm
    · exact absurd he (G.solid_ne_center l)
    · exact congrArg some (G.leftPiece_arm_injective he)
  · intro i
    rcases G.mem_set (hcover i) with hi | ⟨l, hi⟩
    · exact ⟨none, hi.symm⟩
    · exact ⟨some l, hi.symm⟩

include hseams in
theorem wholeArm_bijective : Function.Bijective G.arm := by
  refine ⟨G.arm_injective, fun k => ?_⟩
  obtain ⟨l, hl⟩ := G.internal (hseams k)
  exact ⟨l, hl.symm⟩

include hcover in
theorem wholeExternal_owned (r : Fin T.externalCount) : T.externalPiece r = G.center := by
  rcases G.mem_set (hcover (T.externalPiece r)) with hr | ⟨l, hr⟩
  · exact hr
  · have he := G.side_eq_of_solid l (.inr (.inr r)) hr
    exact False.elim (Sum.inr_ne_inl he)

def wholeCenterSideMap : Fin d.fillingCount ⊕ Fin T.externalCount → T.OwnedSide G.center
  | .inl l => ⟨.inr (.inl (G.arm l)), G.arm_right l⟩
  | .inr r => ⟨.inr (.inr r), G.wholeExternal_owned hcover r⟩

include hseams in
theorem wholeCenterSideMap_bijective : Function.Bijective (G.wholeCenterSideMap hcover) := by
  constructor
  · rintro (l | r) (l' | r') he <;> have hv := congrArg Subtype.val he
    · exact congrArg Sum.inl (G.arm_injective (Sum.inl_injective (Sum.inr_injective hv)))
    · exact False.elim (Sum.inl_ne_inr (Sum.inr_injective hv))
    · exact False.elim (Sum.inr_ne_inl (Sum.inr_injective hv))
    · exact congrArg Sum.inr (Sum.inr_injective (Sum.inr_injective hv))
  · rintro ⟨s, hs⟩
    rcases s with k | k | r
    · obtain ⟨l, rfl⟩ := G.internal (hseams k)
      exact absurd hs (G.solid_ne_center l)
    · obtain ⟨l, rfl⟩ := G.internal (hseams k)
      exact ⟨.inl l, rfl⟩
    · exact ⟨.inr r, rfl⟩

def wholeCenterSideEquiv : Fin d.fillingCount ⊕ Fin T.externalCount ≃ T.OwnedSide G.center :=
  Equiv.ofBijective _ (G.wholeCenterSideMap_bijective hcover hseams)

include G hcover hseams in
theorem wholeExternal_count : T.externalCount = d.ports := by
  have he := Fintype.card_congr (G.wholeCenterSideEquiv hcover hseams)
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, G.product.card_ownedSide] at he
  have hd := d.ports_add_fillingCount
  omega

def wholeBlock : SeifertBlock W d where
  presentation := T
  piece := Equiv.ofBijective G.wholePiece (G.wholePiece_bijective hcover)
  product := G.product
  solid := G.solid
  port := (Equiv.sumComm _ _).trans
    ((Equiv.sumCongr (Equiv.refl _) (finCongr (G.wholeExternal_count hcover hseams).symm)).trans
      ((G.wholeCenterSideEquiv hcover hseams).trans G.product.port.symm))
  seam := Equiv.ofBijective G.arm (G.wholeArm_bijective hseams)
  free := finCongr (G.wholeExternal_count hcover hseams).symm
  free_port r := by
    change (G.product.port (G.product.port.symm _)).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  filled_port l := by
    change (G.product.port (G.product.port.symm _)).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  solid_port l := G.side_eq_of_solid l _ ((G.solid l).port 0).property
  slope := G.slope

end GC.Seifert.SelectedStarGroup

namespace GC.Seifert

abbrev selectedNormalData (q : ℤ) : SeifertData where
  k := 3
  ports := 2
  cones := []
  normals := [q]
  one_le_k := by decide
  k_le_three := le_rfl
  two_le_of_mem_cones c hc := False.elim (List.not_mem_nil hc)
  gcd_eq_one_of_mem_cones c hc := False.elim (List.not_mem_nil hc)
  ports_add_length_add_length := rfl

namespace ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

abbrev fillingSelectedPresentation (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) :
    TorusPresentation (fillingProductCarrier E j) :=
  (E.toTorus.selectedLocal_presentation (E.toTorus.seamPair j) {j}
    (fillingProduct_internal E j) (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    ⟨E.toTorus.leftPiece j, E.toTorus.left_mem_seamPair j⟩).flipSeams (fun _k => !b)

abbrev fillingSelectedIndex (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (_b : Bool) :
    Fin ({j} : Finset (Fin E.toTorus.pairing.count)).card :=
  ⟨0, by simp⟩

def fillingHostIndex (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) :
    Fin (E.toTorus.seamPair j).card :=
  E.toTorus.subIndexOf (E.toTorus.seamPair j)
    ((E.mem_seamPair_iff j b _).mpr (Or.inr rfl))

def fillingSolidIndex (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) :
    Fin (E.toTorus.seamPair j).card :=
  E.toTorus.subIndexOf (E.toTorus.seamPair j)
    ((E.mem_seamPair_iff j b _).mpr (Or.inl rfl))

theorem fillingSelectedPresentation_left (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.fillingSelectedPresentation j b).leftPiece (E.fillingSelectedIndex j b) =
      E.fillingSolidIndex j b := by
  have hj : (E.toTorus.alongSeam {j} (E.fillingSelectedIndex j b)).val = j :=
    Finset.mem_singleton.mp (E.toTorus.alongSeam {j} (E.fillingSelectedIndex j b)).property
  cases b
  · change E.toTorus.restrictRightPiece (E.toTorus.seamPair j)
      (E.toTorus.alongKeptIndex _ {j} (fillingProduct_internal E j)
        (E.fillingSelectedIndex j false)) = _
    unfold TorusPresentation.restrictRightPiece fillingSolidIndex
    apply (E.toTorus.subIndexOf_eq_iff _ _).mpr
    rw [E.toTorus.keptSeam_alongKeptIndex, hj]
    rfl
  · change E.toTorus.restrictLeftPiece (E.toTorus.seamPair j)
      (E.toTorus.alongKeptIndex _ {j} (fillingProduct_internal E j)
        (E.fillingSelectedIndex j true)) = _
    unfold TorusPresentation.restrictLeftPiece fillingSolidIndex
    apply (E.toTorus.subIndexOf_eq_iff _ _).mpr
    rw [E.toTorus.keptSeam_alongKeptIndex, hj]
    rfl

theorem fillingSelectedPresentation_right (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.fillingSelectedPresentation j b).rightPiece (E.fillingSelectedIndex j b) =
      E.fillingHostIndex j b := by
  have hj : (E.toTorus.alongSeam {j} (E.fillingSelectedIndex j b)).val = j :=
    Finset.mem_singleton.mp (E.toTorus.alongSeam {j} (E.fillingSelectedIndex j b)).property
  cases b
  · change E.toTorus.restrictLeftPiece (E.toTorus.seamPair j)
      (E.toTorus.alongKeptIndex _ {j} (fillingProduct_internal E j)
        (E.fillingSelectedIndex j false)) = _
    unfold TorusPresentation.restrictLeftPiece fillingHostIndex
    apply (E.toTorus.subIndexOf_eq_iff _ _).mpr
    rw [E.toTorus.keptSeam_alongKeptIndex, hj]
    rfl
  · change E.toTorus.restrictRightPiece (E.toTorus.seamPair j)
      (E.toTorus.alongKeptIndex _ {j} (fillingProduct_internal E j)
        (E.fillingSelectedIndex j true)) = _
    unfold TorusPresentation.restrictRightPiece fillingHostIndex
    apply (E.toTorus.subIndexOf_eq_iff _ _).mpr
    rw [E.toTorus.keptSeam_alongKeptIndex, hj]
    rfl

theorem fillingSelectedPresentation_matching (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.fillingSelectedPresentation j b).pairing.matching (E.fillingSelectedIndex j b) =
      E.crossMap j b := by
  have hj : (E.toTorus.alongSeam {j} (E.fillingSelectedIndex j b)).val = j :=
    Finset.mem_singleton.mp (E.toTorus.alongSeam {j} (E.fillingSelectedIndex j b)).property
  have hm : (E.toTorus.restrictAlongPairing (E.toTorus.seamPair j) {j}
      (fillingProduct_internal E j)).matching (E.fillingSelectedIndex j b) =
        E.toTorus.pairing.matching j := by
    change E.toTorus.pairing.matching (E.toTorus.keptSeam (E.toTorus.seamPair j)
      (E.toTorus.alongKeptIndex _ {j} (fillingProduct_internal E j)
        (E.fillingSelectedIndex j b))).val = _
    rw [E.toTorus.keptSeam_alongKeptIndex, hj]
  cases b
  · change ((E.toTorus.restrictAlongPairing (E.toTorus.seamPair j) {j}
      (fillingProduct_internal E j)).matching (E.fillingSelectedIndex j false)).symm = _
    exact congrArg Diffeomorph.symm hm
  · exact hm

def fillingSelectedPiece (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) {i : Fin E.toTorus.components.count}
    (hi : i ∈ E.toTorus.seamPair j) {k : ℕ} (P : ProductFibredPiece E.toTorus i k) :
    ProductFibredPiece (E.fillingSelectedPresentation j b)
      (E.toTorus.subIndexOf (E.toTorus.seamPair j) hi) k :=
  (P.transfer (E.toTorus.selectedLocal_transfer (E.toTorus.seamPair j) {j}
    (fillingProduct_internal E j) (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    ⟨E.toTorus.leftPiece j, E.toTorus.left_mem_seamPair j⟩ hi)).flip (fun _k => !b)

def fillingOrientedGroup (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (q : ℤ)
    (hq : E.mergeSlope j b = Merge.sectionSlope q) :
    SelectedStarGroup (E.fillingSelectedPresentation j b) (selectedNormalData q) where
  center := E.fillingHostIndex j b
  product := E.fillingSelectedPiece j b
    ((E.mem_seamPair_iff j b _).mpr (Or.inr rfl)) (E.pieceOfKind hk3)
  arm _l := E.fillingSelectedIndex j b
  solid _l := (E.fillingSelectedPiece j b
    ((E.mem_seamPair_iff j b _).mpr (Or.inl rfl)) (E.pieceOfKind h.kind_seamPiece)).congrIndex
      (E.fillingSelectedPresentation_left j b).symm
  arm_right _l := E.fillingSelectedPresentation_right j b
  arm_injective l l' _he := by
    change Fin 1 at l l'
    exact Subsingleton.elim l l'
  solid_ne_center _l := by
    rw [E.fillingSelectedPresentation_left j b]
    intro he
    exact h.seamPiece_ne_hostPiece ((E.toTorus.subIndexOf_eq_iff _ _).mp he)
  slope l := by
    change Fin 1 at l
    obtain rfl : l = 0 := Subsingleton.elim l 0
    rw [E.fillingSelectedPresentation_matching j b]
    change torusUnit (E.crossMap j b) • meridianSlope = Merge.sectionSlope q
    cases b
    · simpa only [crossMap, mergeSlope, torusUnit_symm] using hq
    · exact hq

theorem fillingOrientedGroup_cover (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (q : ℤ)
    (hq : E.mergeSlope j b = Merge.sectionSlope q) :
    ∀ i, i ∈ (E.fillingOrientedGroup j b h hk3 q hq).set := by
  intro i
  let G := E.fillingOrientedGroup j b h hk3 q hq
  have hm := (E.mem_seamPair_iff j b _).mp
    (E.toTorus.subIndex_mem (E.toTorus.seamPair j) i)
  rcases hm with hs | hh
  · have hi : i = E.fillingSolidIndex j b :=
      (E.toTorus.subIndexOf_subIndex (E.toTorus.seamPair j) i).symm.trans
        ((E.toTorus.subIndexOf_eq_iff _ _).mpr hs)
    have he : G.arm ⟨0, by change 0 < 1; decide⟩ = E.fillingSelectedIndex j b := rfl
    have hi' : i = (E.fillingSelectedPresentation j b).leftPiece
        (G.arm ⟨0, by change 0 < 1; decide⟩) :=
      hi.trans ((E.fillingSelectedPresentation_left j b).symm.trans
        (congrArg (E.fillingSelectedPresentation j b).leftPiece he.symm))
    exact hi' ▸ G.solid_mem ⟨0, by change 0 < 1; decide⟩
  · have hi : i = G.center :=
      (E.toTorus.subIndexOf_subIndex (E.toTorus.seamPair j) i).symm.trans
        ((E.toTorus.subIndexOf_eq_iff _ _).mpr hh)
    exact hi ▸ G.center_mem

theorem fillingOrientedGroup_seams (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (q : ℤ)
    (hq : E.mergeSlope j b = Merge.sectionSlope q) :
    ∀ k, k ∈ (E.fillingOrientedGroup j b h hk3 q hq).selected := by
  intro k
  have he : k = E.fillingSelectedIndex j b := by
    apply Fin.ext
    have hk := k.isLt
    change k.val < ({j} : Finset (Fin E.toTorus.pairing.count)).card at hk
    simp only [Finset.card_singleton] at hk
    change k.val = 0
    omega
  exact he ▸ (E.fillingOrientedGroup j b h hk3 q hq).arm_mem ⟨0, by change 0 < 1; decide⟩

def fillingSelectedBlock (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (q : ℤ)
    (hq : E.mergeSlope j b = Merge.sectionSlope q) :
    SeifertBlock (fillingProductCarrier E j) (selectedNormalData q) :=
  (E.fillingOrientedGroup j b h hk3 q hq).wholeBlock
    (E.fillingOrientedGroup_cover j b h hk3 q hq)
    (E.fillingOrientedGroup_seams j b h hk3 q hq)

theorem fillingSelectedBlock_externalCount (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (q : ℤ)
    (hq : E.mergeSlope j b = Merge.sectionSlope q) :
    (E.fillingSelectedBlock j b h hk3 q hq).presentation.externalCount = 2 :=
  (E.fillingOrientedGroup j b h hk3 q hq).wholeExternal_count
    (E.fillingOrientedGroup_cover j b h hk3 q hq)
    (E.fillingOrientedGroup_seams j b h hk3 q hq)

theorem fillingSelectedBlock_external_collar (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (q : ℤ)
    (hq : E.mergeSlope j b = Merge.sectionSlope q)
    (r : Fin (E.fillingSelectedBlock j b h hk3 q hq).presentation.externalCount)
    (p : Torus × EuclideanHalfSpace 1) :
    (E.fillingSelectedBlock j b h hk3 q hq).presentation.external.collar r p =
      (E.toTorus.restrictAlongBoundaryToriDescended (E.toTorus.seamPair j) {j}
        (fillingProduct_internal E j)
        (TorusPresentation.externalPiece_not_mem_of_closed _ _)).collar r p := rfl

theorem fillingSelectedBlock_matching_linear (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (q : ℤ)
    (hq : E.mergeSlope j b = Merge.sectionSlope q) (hlin : E.IsLinearSeam j) :
    ∀ m, (E.fillingSelectedBlock j b h hk3 q hq).presentation.pairing.matching
        ((E.fillingSelectedBlock j b h hk3 q hq).seam m) =
      linearTorusDiffeomorph (torusUnit
        ((E.fillingSelectedBlock j b h hk3 q hq).presentation.pairing.matching
          ((E.fillingSelectedBlock j b h hk3 q hq).seam m))) := by
  intro m
  change (E.fillingSelectedPresentation j b).pairing.matching (E.fillingSelectedIndex j b) =
    linearTorusDiffeomorph (torusUnit
      ((E.fillingSelectedPresentation j b).pairing.matching (E.fillingSelectedIndex j b)))
  rw [E.fillingSelectedPresentation_matching j b]
  apply Diffeomorph.ext
  intro t
  have ht := hlin.crossMap_apply b t
  have hu : torusUnit (E.crossMap j b) = E.crossUnit j b := by
    cases b
    · exact torusUnit_symm _
    · rfl
  change E.crossMap j b t = linearTorusMap (torusUnit (E.crossMap j b)) t
  rw [hu]
  exact ht

theorem exists_fillingSelectedCharts (hT : TorusMappingClassLinear)
    (E : ElementaryPresentation (NoCuts.carrier Q)) (j : Fin E.toTorus.pairing.count)
    (b : Bool) (h : E.IsMergeSeam j b) (hk3 : E.kind (E.hostPiece j b) = 3) :
    ∃ q : ℤ, E.mergeSlope j b = Merge.sectionSlope q ∧
      Nonempty (SeifertBlockCharts (fillingProductCarrier E j) (selectedNormalData q)) := by
  obtain ⟨q, hq⟩ := h.exists_mergeSlope_eq
  exact ⟨q, hq, (E.fillingSelectedBlock j b h hk3 q hq).exists_charts hT⟩

theorem exists_fillingSelectedCharts_of_linear (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (hlin : E.IsLinearSeam j) :
    ∃ q : ℤ, E.mergeSlope j b = Merge.sectionSlope q ∧
      Nonempty (SeifertBlockCharts (fillingProductCarrier E j) (selectedNormalData q)) := by
  obtain ⟨q, hq⟩ := h.exists_mergeSlope_eq
  exact ⟨q, hq, (E.fillingSelectedBlock j b h hk3 q hq).exists_charts_of_linear
    (E.fillingSelectedBlock_matching_linear j b h hk3 q hq hlin)⟩

theorem fillingSelectedBlock_counts (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (q : ℤ)
    (hq : E.mergeSlope j b = Merge.sectionSlope q) :
    (E.fillingSelectedBlock j b h hk3 q hq).presentation.components.count = 2 ∧
      (E.fillingSelectedBlock j b h hk3 q hq).presentation.pairing.count = 1 ∧
      (E.fillingSelectedBlock j b h hk3 q hq).presentation.externalCount = 2 := by
  refine ⟨?_, ?_, E.fillingSelectedBlock_externalCount j b h hk3 q hq⟩
  · change (E.toTorus.seamPair j).card = 2
    simp [TorusPresentation.seamPair, h.leftPiece_ne_rightPiece]
  · change ({j} : Finset (Fin E.toTorus.pairing.count)).card = 1
    simp

theorem exists_fillingSelectedBlock_on_carrier (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) :
    ∃ q : ℤ, E.mergeSlope j b = Merge.sectionSlope q ∧
      Nonempty (SeifertBlock (fillingProductCarrier E j) (selectedNormalData q)) := by
  obtain ⟨q, hq⟩ := h.exists_mergeSlope_eq
  exact ⟨q, hq, ⟨E.fillingSelectedBlock j b h hk3 q hq⟩⟩

end ElementaryPresentation

end GC.Seifert

namespace GC.Seifert

section Partial
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {K : ModelWithCorners ℝ G H''}
  {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [ChartedSpace H M] [ChartedSpace H' N] [ChartedSpace H'' P]

theorem smoothAt_of_partial_comp (e : PartialDiffeomorph I J M N ∞)
    (f : N → P) {x : M} (hx : x ∈ e.source)
    (hf : ContMDiffAt I K ∞ (f ∘ e) x) : ContMDiffAt J K ∞ f (e x) := by
  have he : e.symm (e x) = x := e.symm_apply_apply hx
  have hs := e.symm.contMDiffOn.contMDiffAt
    (e.open_target.mem_nhds (e.map_source hx))
  have hcomp := (he ▸ hf).comp (e x) hs
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
  exact congrArg f (e.apply_symm_apply hy).symm

variable [Nonempty H] [IsManifold I ∞ M]

def disjointOpensDiffeomorph (U V : TopologicalSpace.Opens M)
    (hdis : Disjoint (U : Set M) (V : Set M)) (hcov : (U : Set M) ∪ V = univ) :
    (U ⊕ V) ≃ₘ⟮I, I⟯ M := by
  let f : U ⊕ V → M := Sum.elim Subtype.val Subtype.val
  have hf : IsLocalDiffeomorph I I ∞ f := by
    intro x
    rcases x with x | x
    · apply DifferentialGeometry.isLocalDiffeomorphAt_of_comp
        (I := I) (J := I) (K := I) (f := Sum.inl) (g := f)
      · exact DifferentialGeometry.isLocalDiffeomorph_subtype_val U x
      · exact isLocalDiffeomorph_sum_inl x
    · apply DifferentialGeometry.isLocalDiffeomorphAt_of_comp
        (I := I) (J := I) (K := I) (f := Sum.inr) (g := f)
      · exact DifferentialGeometry.isLocalDiffeomorph_subtype_val V x
      · exact isLocalDiffeomorph_sum_inr x
  have hinj : Function.Injective f := by
    rintro (x | x) (y | y) he
    · exact congrArg Sum.inl (Subtype.ext he)
    · change x.val = y.val at he
      exact False.elim (Set.disjoint_left.mp hdis x.property (he.symm ▸ y.property))
    · change x.val = y.val at he
      exact False.elim (Set.disjoint_left.mp hdis y.property (he ▸ x.property))
    · exact congrArg Sum.inr (Subtype.ext he)
  have hsur : Function.Surjective f := by
    intro x
    have hx : x ∈ (U : Set M) ∪ V := hcov.symm ▸ mem_univ x
    rcases hx with hx | hx
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  exact hf.diffeomorphOfBijective ⟨hinj, hsur⟩

theorem disjointOpensDiffeomorph_inl (U V : TopologicalSpace.Opens M)
    (hdis : Disjoint (U : Set M) (V : Set M)) (hcov : (U : Set M) ∪ V = univ)
    (x : U) : disjointOpensDiffeomorph (I := I) U V hdis hcov (Sum.inl x) = x.val := rfl

theorem disjointOpensDiffeomorph_inr (U V : TopologicalSpace.Opens M)
    (hdis : Disjoint (U : Set M) (V : Set M)) (hcov : (U : Set M) ∪ V = univ)
    (x : V) : disjointOpensDiffeomorph (I := I) U V hdis hcov (Sum.inr x) = x.val := rfl

end Partial

namespace TorusPairing
variable {C : CompactCarrier.{u}}

theorem rel_iff_params (P : TorusPairing C) (x y : C.Carrier) :
    P.gluing.rel x y ↔ x = y ∨ ∃ k t,
      (x = (P.leftParam k t).val ∧ y = (P.rightParam k (P.matching k t)).val) ∨
        (y = (P.leftParam k t).val ∧ x = (P.rightParam k (P.matching k t)).val) := by
  constructor
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact Or.inl rfl
    · right
      rcases hk with hl | hr
      · let t := (P.leftParam k).symm ⟨x, hl⟩
        have hx : (P.leftParam k t).val = x :=
          congrArg Subtype.val ((P.leftParam k).apply_symm_apply ⟨x, hl⟩)
        refine ⟨k, t, Or.inl ⟨hx.symm, ?_⟩⟩
        rw [P.gluing.flip_of_mem_left hl]
        have hm := congrArg Subtype.val (P.matching_eq k t)
        rwa [show P.leftParam k t = ⟨x, hl⟩ from Subtype.ext hx] at hm
      · let t := (P.matching k).symm ((P.rightParam k).symm ⟨x, hr⟩)
        have hx : P.rightParam k (P.matching k t) = ⟨x, hr⟩ := by
          simp [t]
        refine ⟨k, t, Or.inr ⟨?_, (congrArg Subtype.val hx).symm⟩⟩
        rw [P.gluing.flip_of_mem_right hr]
        have hm := congrArg (P.gluing.attaching k).symm (P.matching_eq k t)
        rw [Homeomorph.symm_apply_apply, hx] at hm
        exact (congrArg Subtype.val hm).symm
  · rintro (rfl | ⟨k, t, ht | ht⟩)
    · exact Or.inl rfl
    · rcases ht with ⟨rfl, rfl⟩
      have h := P.gluing.rel_of_mem_left (P.leftParam k t).property
      simpa only [P.matching_eq] using h
    · rcases ht with ⟨rfl, rfl⟩
      have h := P.gluing.rel_of_mem_left (P.leftParam k t).property
      exact P.gluing.isEquivalence_rel.symm (by simpa only [P.matching_eq] using h)

end TorusPairing

namespace TorusPresentation
variable {W W' : CompactCarrier.{u}}

theorem contMDiff_of_cutMap_seams (T : TorusPresentation W) (f : W.Carrier → W'.Carrier)
    (hcut : ContMDiff T.cutCarrier.model W'.model ∞ (f ∘ T.cutMap))
    (hseam : ∀ k t, ContMDiffAt signedCollarModel W'.model ∞
      (f ∘ T.seam k) (t, 0)) : ContMDiff W.model W'.model ∞ f := by
  intro w
  obtain ⟨x, rfl⟩ := T.cutMap_surjective w
  by_cases hx : T.cutCarrier.model.IsInteriorPoint x
  · let xi : T.cutCarrier.interior := ⟨x, hx⟩
    have hxi : ContMDiffAt T.cutCarrier.model W'.model ∞
        (fun y => f (T.interiorDiffeomorph y).val) xi := by
      have h := hcut.comp (contMDiff_subtype_val (U := T.cutCarrier.interior))
      have he : (fun y => f (T.interiorDiffeomorph y).val) =
          (f ∘ T.cutMap) ∘ Subtype.val := by
        funext y
        rw [T.interior_map]
        rfl
      rw [he]
      exact h xi
    have hs := (T.interiorDiffeomorph.symm_apply_apply xi).symm ▸ hxi
    have hs := hs.comp (T.interiorDiffeomorph xi)
      T.interiorDiffeomorph.symm.contMDiffAt
    have he : (fun y => f (T.interiorDiffeomorph
        (T.interiorDiffeomorph.symm y)).val) = (fun y : T.interiorImage => f y.val) := by
      funext y
      rw [Diffeomorph.apply_symm_apply]
    change ContMDiffAt W.model W'.model ∞
      (fun y => f (T.interiorDiffeomorph (T.interiorDiffeomorph.symm y)).val) _ at hs
    rw [he] at hs
    have hs' := contMDiffAt_subtype_iff.mp hs
    simpa [xi, T.interior_map, TorusPresentation.cutMap] using hs' 
  · have hb : x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier :=
      (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint x).mpr hx
    rw [T.cut_boundary_exhausted] at hb
    rcases hb with hb | hb
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
      have he : ∃ t, T.cutMap x = T.seam k (t, 0) := by
        rcases hk with hl | hr
        · refine ⟨(T.pairing.leftParam k).symm ⟨x, hl⟩, ?_⟩
          rw [T.seam_zero, Homeomorph.apply_symm_apply]
          rfl
        · refine ⟨(T.pairing.matching k).symm
            ((T.pairing.rightParam k).symm ⟨x, hr⟩), ?_⟩
          rw [T.seam_zero]
          change T.reconstruction (T.pairing.quotientMap x) = _
          rw [T.quotientMap_leftParam_eq_rightParam_matching,
            Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
      obtain ⟨t, ht⟩ := he
      rw [ht]
      exact smoothAt_of_partial_comp (T.seam k) f
        (by rw [T.seam_source]; exact ⟨by norm_num, by norm_num⟩) (hseam k t)
    · obtain ⟨r, t, ht⟩ := mem_iUnion.mp hb
      have ht' : T.cutMap x = T.external.collar r (t, halfZero) := by
        rw [← ht]
        exact T.marked_collar r (t, halfZero) (zero_mem_halfCollarSource t)
      rw [ht']
      apply smoothAt_of_partial_comp (T.external.collar r) f
        (by rw [T.external.source_eq]; exact zero_mem_halfCollarSource t)
      have h := hcut.comp_contMDiffOn (T.cutExternal.collar r).contMDiffOn
      have he : EqOn (f ∘ T.external.collar r)
          ((f ∘ T.cutMap) ∘ T.cutExternal.collar r) halfCollarSource := by
        intro p hp
        exact congrArg f (T.marked_collar r p hp).symm
      have h' := h.congr (fun p hp => he ((T.cutExternal.source_eq r) ▸ hp))
      rw [T.cutExternal.source_eq r] at h'
      exact h'.contMDiffAt ((T.external.source_eq r) ▸
        (T.external.collar r).open_source.mem_nhds
          ((T.external.source_eq r).symm ▸ zero_mem_halfCollarSource t))

theorem cutRelation_iff_of_params (T : TorusPresentation W) (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (e : Fin T.pairing.count ≃ Fin D.pairing.count)
    (A : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (hl : ∀ k t, F (T.pairing.leftParam k t).val = (D.pairing.leftParam (e k) (A k t)).val)
    (hr : ∀ k t, F (T.pairing.rightParam k (T.pairing.matching k t)).val =
      (D.pairing.rightParam (e k) (D.pairing.matching (e k) (A k t))).val)
    (x y : T.cutCarrier.Carrier) :
    T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y) := by
  rw [GC.Seifert.TorusPairing.rel_iff_params T.pairing,
    GC.Seifert.TorusPairing.rel_iff_params D.pairing]
  constructor
  · rintro (rfl | ⟨k, t, ht | ht⟩)
    · exact Or.inl rfl
    · rcases ht with ⟨rfl, rfl⟩
      exact Or.inr ⟨e k, A k t, Or.inl ⟨hl k t, hr k t⟩⟩
    · rcases ht with ⟨rfl, rfl⟩
      exact Or.inr ⟨e k, A k t, Or.inr ⟨hl k t, hr k t⟩⟩
  · rintro (hxy | ⟨k, t, ht | ht⟩)
    · exact Or.inl (F.injective hxy)
    · let l := e.symm k
      let r := (A l).symm t
      have hel : e l = k := e.apply_symm_apply k
      have har : A l r = t := (A l).apply_symm_apply t
      have hle := hl l r
      have hre := hr l r
      rw [hel, har] at hle hre
      exact Or.inr ⟨l, r, Or.inl
        ⟨F.injective (ht.1.trans hle.symm), F.injective (ht.2.trans hre.symm)⟩⟩
    · let l := e.symm k
      let r := (A l).symm t
      have hel : e l = k := e.apply_symm_apply k
      have har : A l r = t := (A l).apply_symm_apply t
      have hle := hl l r
      have hre := hr l r
      rw [hel, har] at hle hre
      exact Or.inr ⟨l, r, Or.inr
        ⟨F.injective (ht.1.trans hle.symm), F.injective (ht.2.trans hre.symm)⟩⟩

def cutComparisonHomeomorph (T : TorusPresentation W) (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y)) :
    W.Carrier ≃ₜ W'.Carrier :=
  (T.reconstruction.symm.trans (Homeomorph.Quotient.congr
    (rY := D.pairing.gluing.setoid) F.toHomeomorph hrel)).trans
    D.reconstruction

theorem cutComparisonHomeomorph_cutMap (T : TorusPresentation W) (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y))
    (x : T.cutCarrier.Carrier) :
    T.cutComparisonHomeomorph D F hrel (T.cutMap x) = D.cutMap (F x) := by
  change D.reconstruction ((Homeomorph.Quotient.congr
    (rY := D.pairing.gluing.setoid) F.toHomeomorph hrel)
    (T.reconstruction.symm (T.reconstruction (T.pairing.quotientMap x)))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

def cutComparisonDiffeomorph (T : TorusPresentation W) (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y))
    (hseam : ∀ k t, ContMDiffAt signedCollarModel W'.model ∞
      (T.cutComparisonHomeomorph D F hrel ∘ T.seam k) (t, 0))
    (hback : ∀ k t, ContMDiffAt signedCollarModel W.model ∞
      ((T.cutComparisonHomeomorph D F hrel).symm ∘ D.seam k) (t, 0)) :
    W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier where
  toFun := T.cutComparisonHomeomorph D F hrel
  invFun := (T.cutComparisonHomeomorph D F hrel).symm
  left_inv := (T.cutComparisonHomeomorph D F hrel).symm_apply_apply
  right_inv := (T.cutComparisonHomeomorph D F hrel).apply_symm_apply
  contMDiff_toFun := T.contMDiff_of_cutMap_seams _ (by
    change ContMDiff T.cutCarrier.model W'.model ∞
      (T.cutComparisonHomeomorph D F hrel ∘ T.cutMap)
    have he : T.cutComparisonHomeomorph D F hrel ∘ T.cutMap = D.cutMap ∘ F := by
      funext x
      exact T.cutComparisonHomeomorph_cutMap D F hrel x
    rw [he]
    exact D.quotient_smooth.comp F.contMDiff) hseam
  contMDiff_invFun := D.contMDiff_of_cutMap_seams _ (by
    change ContMDiff D.cutCarrier.model W.model ∞
      ((T.cutComparisonHomeomorph D F hrel).symm ∘ D.cutMap)
    have he : (T.cutComparisonHomeomorph D F hrel).symm ∘ D.cutMap =
        T.cutMap ∘ F.symm := by
      funext y
      apply (T.cutComparisonHomeomorph D F hrel).injective
      rw [Function.comp_apply, Homeomorph.apply_symm_apply,
        Function.comp_apply, T.cutComparisonHomeomorph_cutMap,
        Diffeomorph.apply_symm_apply]
    rw [he]
    exact T.quotient_smooth.comp F.symm.contMDiff) hback

theorem cutComparisonHomeomorph_seam_of_collars (T : TorusPresentation W)
    (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y))
    (e : Fin T.pairing.count ≃ Fin D.pairing.count)
    (A : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (δ : ℝ) (hδ : δ ≤ 1)
    (hl : ∀ k t r (hr0 : 0 ≤ r), r < δ →
      F (T.pairing.leftCollar k (t, halfPoint r hr0)) =
        D.pairing.leftCollar (e k) (A k t, halfPoint r hr0))
    (hr : ∀ k t r (hr0 : 0 ≤ r), r < δ →
      F (T.pairing.rightCollar k (T.pairing.matching k t, halfPoint r hr0)) =
        D.pairing.rightCollar (e k)
          (D.pairing.matching (e k) (A k t), halfPoint r hr0))
    (k : Fin T.pairing.count) (t : Torus) {s : ℝ} (hs : |s| < δ) :
    T.cutComparisonHomeomorph D F hrel (T.seam k (t, s)) = D.seam (e k) (A k t, s) := by
  have hs1 : |s| < 1 := lt_of_lt_of_le hs hδ
  by_cases hpos : 0 ≤ s
  · rw [T.seam_positive k t s hpos (lt_of_le_of_lt (le_abs_self s) hs1),
      D.seam_positive (e k) (A k t) s hpos (lt_of_le_of_lt (le_abs_self s) hs1)]
    change T.cutComparisonHomeomorph D F hrel (T.cutMap _) = D.cutMap _
    rw [T.cutComparisonHomeomorph_cutMap,
      hr k t s hpos (lt_of_le_of_lt (le_abs_self s) hs)]
  · have hneg : s ≤ 0 := le_of_not_ge hpos
    have hslo : -1 < s := (abs_lt.mp hs1).1
    rw [T.seam_negative k t s hneg hslo, D.seam_negative (e k) (A k t) s hneg hslo]
    change T.cutComparisonHomeomorph D F hrel (T.cutMap _) = D.cutMap _
    rw [T.cutComparisonHomeomorph_cutMap,
      hl k t (-s) (neg_nonneg.mpr hneg) (lt_of_le_of_lt (neg_le_abs s) hs)]

def cutComparisonDiffeomorph_of_seamGerms (T : TorusPresentation W)
    (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y))
    (e : Fin T.pairing.count ≃ Fin D.pairing.count)
    (A : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (δ : ℝ) (hδ : 0 < δ)
    (heq : ∀ k t s, |s| < δ →
      T.cutComparisonHomeomorph D F hrel (T.seam k (t, s)) =
        D.seam (e k) (A k t, s)) : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier := by
  have hnhds (t : Torus) : {p : Torus × ℝ | |p.2| < δ} ∈ nhds (t, 0) :=
    (isOpen_lt continuous_snd.abs continuous_const).mem_nhds (by simpa using hδ)
  apply T.cutComparisonDiffeomorph D F hrel
  · intro k t
    have ha : ContMDiff signedCollarModel signedCollarModel ∞
        (fun p : Torus × ℝ => (A k p.1, p.2)) :=
      ((A k).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    have hs := (D.seam (e k)).contMDiffOn.contMDiffAt
      ((D.seam (e k)).open_source.mem_nhds (by
        rw [D.seam_source]
        exact ⟨by norm_num, by norm_num⟩ : (A k t, 0) ∈ (D.seam (e k)).source))
    have h := hs.comp (t, 0) (ha (t, 0))
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hnhds t] with p hp
    exact heq k p.1 p.2 hp
  · intro k t
    let l := e.symm k
    have ha : ContMDiff signedCollarModel signedCollarModel ∞
        (fun p : Torus × ℝ => ((A l).symm p.1, p.2)) :=
      ((A l).symm.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    have hs := (T.seam l).contMDiffOn.contMDiffAt
      ((T.seam l).open_source.mem_nhds (by
        rw [T.seam_source]
        exact ⟨by norm_num, by norm_num⟩ : ((A l).symm t, 0) ∈ (T.seam l).source))
    have h := hs.comp (t, 0) (ha (t, 0))
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hnhds t] with p hp
    have hg := heq l ((A l).symm p.1) p.2 hp
    rw [Diffeomorph.apply_symm_apply, show e l = k from e.apply_symm_apply k] at hg
    exact (congrArg (T.cutComparisonHomeomorph D F hrel).symm hg).symm.trans
      ((T.cutComparisonHomeomorph D F hrel).symm_apply_apply _)

end TorusPresentation
end GC.Seifert

namespace GC.Seifert

def normalFillingIndex (q : ℤ) : Fin (selectedNormalData q).fillingCount :=
  ⟨0, by simp [SeifertData.fillingCount]⟩

structure NormalFillingTrivializations {W : CompactCarrier.{u}} {q : ℤ}
    (B : SeifertBlock W (selectedNormalData q)) where
  hostDepth : ℝ
  hostDepth_pos : 0 < hostDepth
  solidDepth : ℝ
  solidDepth_pos : 0 < solidDepth
  basis : GL (Fin 2) ℤ
  matrix_eq : ((torusUnit (B.presentation.pairing.matching
    (B.seam (normalFillingIndex q))) * basis : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-1, 0; -q, 1]
  host : (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
    B.presentation.cutCarrier.model⟯ B.presentation.components.piece (B.piece none)
  solid : (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
    B.presentation.cutCarrier.model⟯
      B.presentation.components.piece (B.piece (some (normalFillingIndex q)))
  host_collar : ∀ l p, p ∈ halfCollarSource → p.2.val 0 < hostDepth →
    B.presentation.pieceCollar (B.piece none) (B.product.port l) p =
      host ((planarBase 3 (Or.inr rfl)).collar l (p.1.1, p.2), p.1.2)
  solid_collar : ∀ l t s, (t, s) ∈ halfCollarSource → s.val 0 < solidDepth →
    B.presentation.pieceCollar (B.piece (some (normalFillingIndex q)))
      ((B.solid (normalFillingIndex q)).port l) (linearTorusMap basis t, s) =
        solid ((discPlanarBase 1).collar l (t.1, s), t.2)

theorem SeifertBlock.exists_normalFillingTrivializations {W : CompactCarrier.{u}} {q : ℤ}
    (B : SeifertBlock W (selectedNormalData q)) : Nonempty (NormalFillingTrivializations B) := by
  obtain ⟨δH, hδH, ΘH, hH⟩ := B.product.exists_standard_germ (planarBase 3 (Or.inr rfl))
  have hc : (torusMatrix (B.presentation.pairing.matching (B.seam (normalFillingIndex q))) 0 0,
      torusMatrix (B.presentation.pairing.matching (B.seam (normalFillingIndex q))) 1 0) =
      (1, q) ∨
      (torusMatrix (B.presentation.pairing.matching (B.seam (normalFillingIndex q))) 0 0,
        torusMatrix (B.presentation.pairing.matching (B.seam (normalFillingIndex q))) 1 0) =
        -(1, q) := by
    have hd : (selectedNormalData q).fillingSlope (normalFillingIndex q) = (1, q) := by
      change Fin.append (fun c : Fin 0 => (( ([] : List (ℕ × ℤ))[c].1 : ℤ),
        ([] : List (ℕ × ℤ))[c].2)) (fun _n : Fin 1 => (1, q)) (Fin.natAdd 0 0) = _
      rw [Fin.append_right]
    simpa only [hd] using B.torusMatrix_meridian (normalFillingIndex q)
  obtain ⟨C, Φ, hC, hΦ⟩ := exists_solidBasis_normalization
    (torusUnit (B.presentation.pairing.matching (B.seam (normalFillingIndex q))))
    1 q 0 1 (by ring) hc
  obtain ⟨δS, hδS, ΘS, hS⟩ := (B.solid (normalFillingIndex q)).exists_basis_germ 1 C Φ hΦ
  exact ⟨⟨δH, hδH, δS, hδS, C, hC, ΘH, ΘS, hH, hS⟩⟩

end GC.Seifert

namespace GC.Seifert

variable {W : CompactCarrier.{u}} {q : ℤ}

theorem SeifertBlock.normalPieces_cover (B : SeifertBlock W (selectedNormalData q)) :
    (B.presentation.components.piece (B.piece none) : Set B.presentation.cutCarrier.Carrier) ∪
      B.presentation.components.piece (B.piece (some (normalFillingIndex q))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ i, (B.presentation.components.piece i :
      Set B.presentation.cutCarrier.Carrier) := B.presentation.components.covers.symm ▸ mem_univ x
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨r, rfl⟩ := B.piece.surjective i
  rcases r with _ | m
  · exact Or.inl hi
  · have hm : m = normalFillingIndex q := by
      apply Fin.ext
      have hb : m.val < 1 := by
        simpa only [SeifertData.fillingCount, List.length_nil, List.length_singleton,
          Nat.zero_add] using m.isLt
      exact Nat.lt_one_iff.mp hb
    subst m
    exact Or.inr hi

def NormalFillingTrivializations.cutDiffeomorph
    {B : SeifertBlock W (selectedNormalData q)} (X : NormalFillingTrivializations B) :
    ConeFilling.FilledCut.{u} ≃ₘ⟮𝓡∂ 3, B.presentation.cutCarrier.model⟯
      B.presentation.cutCarrier.Carrier := by
  let H : productSet.{u} 3 ≃ₘ⟮𝓡∂ 3, B.presentation.cutCarrier.model⟯
      B.presentation.components.piece (B.piece none) :=
    (productDiffeomorph 3).symm.trans X.host
  let V : solidSet.{u} ≃ₘ⟮𝓡∂ 3, B.presentation.cutCarrier.model⟯
      B.presentation.components.piece (B.piece (some (normalFillingIndex q))) :=
    solidDiffeomorph.symm.trans X.solid
  let Z : ConeFilling.FilledCut.{u} ≃ₘ⟮𝓡∂ 3, B.presentation.cutCarrier.model⟯
      ((B.presentation.components.piece (B.piece none)) ⊕
        (B.presentation.components.piece (B.piece (some (normalFillingIndex q))))) :=
    { toEquiv := Equiv.sumCongr H.toEquiv V.toEquiv
      contMDiff_toFun := H.contMDiff.sumMap V.contMDiff
      contMDiff_invFun := H.symm.contMDiff.sumMap V.symm.contMDiff }
  exact Z.trans
    (disjointOpensDiffeomorph (I := B.presentation.cutCarrier.model)
      (B.presentation.components.piece (B.piece none))
      (B.presentation.components.piece (B.piece (some (normalFillingIndex q))))
      (B.presentation.components.disjoint (by
        intro he
        have hf := B.piece.injective he
        cases hf))
      B.normalPieces_cover)

theorem NormalFillingTrivializations.cutDiffeomorph_inl
    {B : SeifertBlock W (selectedNormalData q)} (X : NormalFillingTrivializations B)
    (x : productSet.{u} 3) : X.cutDiffeomorph (Sum.inl x) =
      (X.host ((productDiffeomorph 3).symm x)).val := rfl

theorem NormalFillingTrivializations.cutDiffeomorph_inr
    {B : SeifertBlock W (selectedNormalData q)} (X : NormalFillingTrivializations B)
    (x : solidSet.{u}) : X.cutDiffeomorph (Sum.inr x) =
      (X.solid (solidDiffeomorph.symm x)).val := rfl

end GC.Seifert

namespace GC.Seifert
variable {W : CompactCarrier.{u}} {q : ℤ}
  {B : SeifertBlock W (selectedNormalData q)}

theorem NormalFillingTrivializations.model_leftCollar (X : NormalFillingTrivializations B)
    (t : Torus) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : r < X.solidDepth) :
    X.cutDiffeomorph ((Merge.sectionFilling q).filledPresentation.pairing.leftCollar 0
      (t, halfPoint r hr0)) =
        B.presentation.pairing.leftCollar (B.seam (normalFillingIndex q))
          (linearTorusMap X.basis t, halfPoint r hr0) := by
  have hp : (t, halfPoint r hr0) ∈ halfCollarSource := hr1
  have hp' : (linearTorusMap X.basis t, halfPoint r hr0) ∈ halfCollarSource := hr1
  have h := congrArg Subtype.val (X.solid_collar 0 t (halfPoint r hr0) hp hr)
  rw [TorusPresentation.pieceCollar_apply _ _ _ hp', B.solid_port] at h
  change B.presentation.pairing.leftCollar (B.seam (normalFillingIndex q))
    (linearTorusMap X.basis t, halfPoint r hr0) = _ at h
  change X.cutDiffeomorph (Sum.inr (solidDiffeomorph
    ((discPlanarBase 1).collar 0 (t.1, halfPoint r hr0), t.2))) = _
  rw [X.cutDiffeomorph_inr, Diffeomorph.symm_apply_apply]
  exact h.symm

theorem NormalFillingTrivializations.matching_basis (X : NormalFillingTrivializations B)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q))))) (t : Torus) :
    B.presentation.pairing.matching (B.seam (normalFillingIndex q))
        (linearTorusMap X.basis t) = (Merge.sectionFilling q).matching t := by
  rw [hlin]
  change linearTorusMap (torusUnit
    (B.presentation.pairing.matching (B.seam (normalFillingIndex q))))
      (linearTorusMap X.basis t) = linearTorusMap (Merge.sectionFilling q).matchingMatrix t
  rw [← linearTorusMap_mul]
  have hm : (Merge.sectionFilling q).matchingMatrix = !![-1, 0; -q, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ConeFilling.matchingMatrix, ConeFilling.reflectMatrix,
        ConeFilling.chartMatrix, Merge.sectionFilling, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hm]
  change linearTorusMap ((torusUnit
    (B.presentation.pairing.matching (B.seam (normalFillingIndex q))) * X.basis :
      GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) t = _
  rw [X.matrix_eq]

theorem NormalFillingTrivializations.model_rightCollar (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 1)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))
    (t : Torus) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : r < X.hostDepth) :
    X.cutDiffeomorph ((Merge.sectionFilling q).filledPresentation.pairing.rightCollar 0
      ((Merge.sectionFilling q).matching t, halfPoint r hr0)) =
        B.presentation.pairing.rightCollar (B.seam (normalFillingIndex q))
          (B.presentation.pairing.matching (B.seam (normalFillingIndex q))
            (linearTorusMap X.basis t), halfPoint r hr0) := by
  let τ := (Merge.sectionFilling q).matching t
  have hp : (τ, halfPoint r hr0) ∈ halfCollarSource := hr1
  have h := congrArg Subtype.val (X.host_collar (B.port (.inr (normalFillingIndex q)))
    (τ, halfPoint r hr0) hp hr)
  rw [TorusPresentation.pieceCollar_apply _ _ _ hp, B.filled_port, hport] at h
  change B.presentation.pairing.rightCollar (B.seam (normalFillingIndex q))
    (τ, halfPoint r hr0) = _ at h
  change X.cutDiffeomorph (Sum.inl (productDiffeomorph 3
    ((planarBase 3 (Or.inr rfl)).collar 1 (τ.1, halfPoint r hr0), τ.2))) = _
  rw [X.cutDiffeomorph_inl, Diffeomorph.symm_apply_apply]
  rw [X.matching_basis hlin t]
  exact h.symm

end GC.Seifert

namespace GC.Seifert
variable {W : CompactCarrier.{u}} {q : ℤ}
  {B : SeifertBlock W (selectedNormalData q)}

def normalSeamEquiv (B : SeifertBlock W (selectedNormalData q)) :
    Fin 1 ≃ Fin B.presentation.pairing.count :=
  (finCongr (by simp [SeifertData.fillingCount])).trans B.seam

theorem normalSeamEquiv_zero (B : SeifertBlock W (selectedNormalData q)) :
    normalSeamEquiv B 0 = B.seam (normalFillingIndex q) := rfl

def NormalFillingTrivializations.innerModelDiffeomorph (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 1)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q))))) :
    (Merge.sectionFilling q).filledSet.{u} ≃ₘ⟮𝓡∂ 3, W.model⟯ W.Carrier := by
  let T := (Merge.sectionFilling q).filledPresentation.{u}
  let e : Fin T.pairing.count ≃ Fin B.presentation.pairing.count := normalSeamEquiv B
  let A : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :=
    fun _k => linearTorusDiffeomorph X.basis
  have hl : ∀ k t, X.cutDiffeomorph (T.pairing.leftParam k t).val =
      (B.presentation.pairing.leftParam (e k) (A k t)).val := by
    intro k t
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rw [← T.pairing.left_zero, ← B.presentation.pairing.left_zero]
    exact X.model_leftCollar t 0 (by norm_num) (by norm_num) X.solidDepth_pos
  have hr : ∀ k t, X.cutDiffeomorph (T.pairing.rightParam k (T.pairing.matching k t)).val =
      (B.presentation.pairing.rightParam (e k)
        (B.presentation.pairing.matching (e k) (A k t))).val := by
    intro k t
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rw [← T.pairing.right_zero, ← B.presentation.pairing.right_zero]
    exact X.model_rightCollar hport hlin t 0 (by norm_num) (by norm_num) X.hostDepth_pos
  have hrel := T.cutRelation_iff_of_params B.presentation X.cutDiffeomorph e A hl hr
  let δ := min 1 (min X.solidDepth X.hostDepth)
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min X.solidDepth_pos X.hostDepth_pos)
  apply T.cutComparisonDiffeomorph_of_seamGerms B.presentation X.cutDiffeomorph hrel e A δ hδ
  intro k t s hs
  apply T.cutComparisonHomeomorph_seam_of_collars B.presentation X.cutDiffeomorph hrel e A
    δ (min_le_left _ _) ?_ ?_ k t hs
  · intro l τ r hr0 hrd
    have hl0 : l = 0 := Subsingleton.elim _ _
    subst l
    exact X.model_leftCollar τ r hr0
      (lt_of_lt_of_le hrd (min_le_left _ _))
      (lt_of_lt_of_le hrd ((min_le_right _ _).trans (min_le_left _ _)))
  · intro l τ r hr0 hrd
    have hl0 : l = 0 := Subsingleton.elim _ _
    subst l
    exact X.model_rightCollar hport hlin τ r hr0
      (lt_of_lt_of_le hrd (min_le_left _ _))
      (lt_of_lt_of_le hrd ((min_le_right _ _).trans (min_le_right _ _)))

end GC.Seifert

namespace GC.Seifert
open ElementaryPresentation

def fillingCircleMulDiffeomorph (c : Circle) : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toFun v := c * v
  invFun v := c⁻¹ * v
  left_inv _v := by simp
  right_inv _v := by simp
  contMDiff_toFun := contMDiff_const.mul contMDiff_id
  contMDiff_invFun := contMDiff_const.mul contMDiff_id

def fillingDiscNegDiffeomorph : discSet.{u} ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ discSet.{u} where
  toFun x := ⟨ULift.up (-x.val.down), by
    rw [mem_discSet_iff, norm_neg]
    exact (mem_discSet_iff x.val).mp x.property⟩
  invFun x := ⟨ULift.up (-x.val.down), by
    rw [mem_discSet_iff, norm_neg]
    exact (mem_discSet_iff x.val).mp x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply ULift.ext
    exact neg_neg _
  right_inv x := by
    apply Subtype.ext
    apply ULift.ext
    exact neg_neg _
  contMDiff_toFun := (discAtlas.contMDiff_iff_subtype_val _).mpr
    (contMDiff_planeLift_up.comp contMDiff_discSet_down.neg)
  contMDiff_invFun := (discAtlas.contMDiff_iff_subtype_val _).mpr
    (contMDiff_planeLift_up.comp contMDiff_discSet_down.neg)

theorem fillingDiscNegDiffeomorph_collar (p : Circle × EuclideanHalfSpace 1) :
    fillingDiscNegDiffeomorph ((discPlanarBase 1).collar 0 p) =
      (discPlanarBase 1).collar 0 (cappingCircleNeg p.1, p.2) := by
  apply Subtype.ext
  apply ULift.ext
  change -(seamRadius 1 (-min (p.2.val 0) 1) • (p.1 : ℂ)) =
    seamRadius 1 (-min (p.2.val 0) 1) • (cappingCircleNeg p.1 : ℂ)
  rw [cappingCircleNeg_coe, smul_neg]

def fillingNegUnit : Circle := cappingCircleNeg 1

theorem cappingCircleNeg_mul (t : Circle) : cappingCircleNeg t = fillingNegUnit * t := by
  apply Circle.ext
  rw [cappingCircleNeg_coe, Circle.coe_mul]
  change -(t : ℂ) = (cappingCircleNeg 1 : ℂ) * (t : ℂ)
  rw [cappingCircleNeg_coe, Circle.coe_one]
  ring

theorem fillingNegUnit_inv : fillingNegUnit⁻¹ = fillingNegUnit := by
  apply Circle.ext
  rw [Circle.coe_inv_eq_conj]
  change starRingEnd ℂ (cappingCircleNeg 1 : ℂ) = (cappingCircleNeg 1 : ℂ)
  rw [cappingCircleNeg_coe, Circle.coe_one]
  simp

def fillingNegTorus (q : ℤ) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  cappingCircleNegDiffeomorph.prodCongr (fillingCircleMulDiffeomorph (fillingNegUnit ^ q))

theorem sectionFilling_matching_neg (q : ℤ) (t : Torus) :
    (Merge.sectionFilling q).matching (fillingNegTorus q t) =
      (cappingCircleNeg ((Merge.sectionFilling q).matching t).1,
        ((Merge.sectionFilling q).matching t).2) := by
  have hm (p : Torus) : (Merge.sectionFilling q).matching p = (p.1⁻¹, p.1 ^ (-q) * p.2) := by
    apply Prod.ext
    · simp [ConeFilling.matching_apply, ConeFilling.matchingMatrix, ConeFilling.reflectMatrix,
        ConeFilling.chartMatrix, Merge.sectionFilling, linearTorusMap,
        Matrix.mul_apply, Fin.sum_univ_two]
    · simp [ConeFilling.matching_apply, ConeFilling.matchingMatrix, ConeFilling.reflectMatrix,
        ConeFilling.chartMatrix, Merge.sectionFilling, linearTorusMap,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [hm, hm, cappingCircleNeg_mul]
  change ((cappingCircleNeg t.1)⁻¹,
    (cappingCircleNeg t.1) ^ (-q) * (fillingNegUnit ^ q * t.2)) = _
  rw [cappingCircleNeg_mul, mul_inv_rev, fillingNegUnit_inv, mul_zpow]
  apply Prod.ext
  · exact mul_comm _ _
  · calc
      (fillingNegUnit ^ (-q) * t.1 ^ (-q)) * (fillingNegUnit ^ q * t.2) =
          (fillingNegUnit ^ (-q) * fillingNegUnit ^ q) * (t.1 ^ (-q) * t.2) := by ac_rfl
      _ = t.1 ^ (-q) * t.2 := by rw [← zpow_add, neg_add_cancel, zpow_zero, one_mul]

def fillingNegCutDiffeomorph (q : ℤ) :
    ConeFilling.FilledCut.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ConeFilling.FilledCut.{u} :=
  (((productDiffeomorph 3).symm.trans
    (cappingPantsNegDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))).trans
      (productDiffeomorph 3)).sumCongr
    ((solidDiffeomorph.symm.trans
      (fillingDiscNegDiffeomorph.prodCongr
        (fillingCircleMulDiffeomorph (fillingNegUnit ^ q)))).trans solidDiffeomorph)

variable {W : CompactCarrier.{u}} {q : ℤ}
  {B : SeifertBlock W (selectedNormalData q)}

def NormalFillingTrivializations.innerTwoCutDiffeomorph
    (X : NormalFillingTrivializations B) :
    ConeFilling.FilledCut.{u} ≃ₘ⟮𝓡∂ 3, B.presentation.cutCarrier.model⟯
      B.presentation.cutCarrier.Carrier :=
  (fillingNegCutDiffeomorph q).trans X.cutDiffeomorph

def NormalFillingTrivializations.innerTwoTorus (X : NormalFillingTrivializations B) :
    Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  (fillingNegTorus q).trans (linearTorusDiffeomorph X.basis)

theorem fillingNegCutDiffeomorph_leftCollar (q : ℤ) (p : Torus × EuclideanHalfSpace 1) :
    fillingNegCutDiffeomorph q
      ((Merge.sectionFilling q).filledPresentation.pairing.leftCollar 0 p) =
        (Merge.sectionFilling q).filledPresentation.pairing.leftCollar 0
          (fillingNegTorus q p.1, p.2) := by
  change Sum.inr (solidDiffeomorph
    (fillingDiscNegDiffeomorph ((discPlanarBase 1).collar 0 (p.1.1, p.2)),
      fillingNegUnit ^ q * p.1.2)) = _
  rw [fillingDiscNegDiffeomorph_collar]
  rfl

theorem NormalFillingTrivializations.modelTwo_leftCollar (X : NormalFillingTrivializations B)
    (t : Torus) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : r < X.solidDepth) :
    X.innerTwoCutDiffeomorph ((Merge.sectionFilling q).filledPresentation.pairing.leftCollar 0
      (t, halfPoint r hr0)) =
        B.presentation.pairing.leftCollar (B.seam (normalFillingIndex q))
          (X.innerTwoTorus t, halfPoint r hr0) := by
  rw [NormalFillingTrivializations.innerTwoCutDiffeomorph]
  change X.cutDiffeomorph (fillingNegCutDiffeomorph q
    ((Merge.sectionFilling q).filledPresentation.pairing.leftCollar 0
      (t, halfPoint r hr0))) = B.presentation.pairing.leftCollar
        (B.seam (normalFillingIndex q))
          (linearTorusMap X.basis (fillingNegTorus q t), halfPoint r hr0)
  rw [fillingNegCutDiffeomorph_leftCollar]
  exact X.model_leftCollar (fillingNegTorus q t) r hr0 hr1 hr

theorem NormalFillingTrivializations.modelTwo_rightCollar (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 2)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))
    (t : Torus) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : r < X.hostDepth) :
    X.innerTwoCutDiffeomorph ((Merge.sectionFilling q).filledPresentation.pairing.rightCollar 0
      ((Merge.sectionFilling q).matching t, halfPoint r hr0)) =
        B.presentation.pairing.rightCollar (B.seam (normalFillingIndex q))
          (B.presentation.pairing.matching (B.seam (normalFillingIndex q))
            (X.innerTwoTorus t), halfPoint r hr0) := by
  let τ : Torus := (cappingCircleNeg ((Merge.sectionFilling q).matching t).1,
    ((Merge.sectionFilling q).matching t).2)
  have hp : (τ, halfPoint r hr0) ∈ halfCollarSource := hr1
  have h := congrArg Subtype.val (X.host_collar (B.port (.inr (normalFillingIndex q)))
    (τ, halfPoint r hr0) hp hr)
  rw [TorusPresentation.pieceCollar_apply _ _ _ hp, B.filled_port, hport] at h
  change B.presentation.pairing.rightCollar (B.seam (normalFillingIndex q))
    (τ, halfPoint r hr0) = _ at h
  change X.cutDiffeomorph (Sum.inl (productDiffeomorph 3
    (cappingPantsNegDiffeomorph ((planarBase 3 (Or.inr rfl)).collar 1
      (((Merge.sectionFilling q).matching t).1, halfPoint r hr0)),
      ((Merge.sectionFilling q).matching t).2))) = _
  rw [X.cutDiffeomorph_inl, Diffeomorph.symm_apply_apply]
  change (X.host (cappingPantsNegDiffeomorph (planarCollar 3 (Or.inr rfl) 1
    (((Merge.sectionFilling q).matching t).1, halfPoint r hr0)),
      ((Merge.sectionFilling q).matching t).2)).val = _
  rw [cappingPantsNeg_collar_one]
  change _ = B.presentation.pairing.rightCollar (B.seam (normalFillingIndex q))
    (B.presentation.pairing.matching (B.seam (normalFillingIndex q))
      (linearTorusMap X.basis (fillingNegTorus q t)), halfPoint r hr0)
  rw [X.matching_basis hlin, sectionFilling_matching_neg]
  exact h.symm

def NormalFillingTrivializations.innerTwoModelDiffeomorph (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 2)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q))))) :
    (Merge.sectionFilling q).filledSet.{u} ≃ₘ⟮𝓡∂ 3, W.model⟯ W.Carrier := by
  let T := (Merge.sectionFilling q).filledPresentation.{u}
  let e : Fin T.pairing.count ≃ Fin B.presentation.pairing.count := normalSeamEquiv B
  let A : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :=
    fun _k => X.innerTwoTorus
  have hl : ∀ k t, X.innerTwoCutDiffeomorph (T.pairing.leftParam k t).val =
      (B.presentation.pairing.leftParam (e k) (A k t)).val := by
    intro k t
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rw [← T.pairing.left_zero, ← B.presentation.pairing.left_zero]
    exact X.modelTwo_leftCollar t 0 (by norm_num) (by norm_num) X.solidDepth_pos
  have hr : ∀ k t, X.innerTwoCutDiffeomorph (T.pairing.rightParam k (T.pairing.matching k t)).val =
      (B.presentation.pairing.rightParam (e k)
        (B.presentation.pairing.matching (e k) (A k t))).val := by
    intro k t
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rw [← T.pairing.right_zero, ← B.presentation.pairing.right_zero]
    exact X.modelTwo_rightCollar hport hlin t 0 (by norm_num) (by norm_num) X.hostDepth_pos
  have hrel := T.cutRelation_iff_of_params B.presentation X.innerTwoCutDiffeomorph e A hl hr
  let δ := min 1 (min X.solidDepth X.hostDepth)
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min X.solidDepth_pos X.hostDepth_pos)
  apply T.cutComparisonDiffeomorph_of_seamGerms B.presentation X.innerTwoCutDiffeomorph
    hrel e A δ hδ
  intro k t s hs
  apply T.cutComparisonHomeomorph_seam_of_collars B.presentation X.innerTwoCutDiffeomorph hrel e A
    δ (min_le_left _ _) ?_ ?_ k t hs
  · intro l τ r hr0 hrd
    have hl0 : l = 0 := Subsingleton.elim _ _
    subst l
    exact X.modelTwo_leftCollar τ r hr0
      (lt_of_lt_of_le hrd (min_le_left _ _))
      (lt_of_lt_of_le hrd ((min_le_right _ _).trans (min_le_left _ _)))
  · intro l τ r hr0 hrd
    have hl0 : l = 0 := Subsingleton.elim _ _
    subst l
    exact X.modelTwo_rightCollar hport hlin τ r hr0
      (lt_of_lt_of_le hrd (min_le_left _ _))
      (lt_of_lt_of_le hrd ((min_le_right _ _).trans (min_le_right _ _)))


end GC.Seifert

namespace GC.Seifert

theorem SeifertBlock.exists_innerNormalAnnulusProduct {W : CompactCarrier.{u}} {q : ℤ}
    (B : SeifertBlock W (selectedNormalData q))
    (hport : B.port (.inr (normalFillingIndex q)) ≠ 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q))))) :
    Nonempty ((planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), W.model⟯ W.Carrier) := by
  obtain ⟨X⟩ := B.exists_normalFillingTrivializations
  rcases ConeFilling.fin_three_cases (B.port (.inr (normalFillingIndex q))) with hp | hp | hp
  · exact (hport hp).elim
  · exact ⟨(ElementaryPresentation.sectionCappingAnnulusProductDiffeomorph q).trans
      (X.innerModelDiffeomorph hp hlin)⟩
  · exact ⟨(ElementaryPresentation.sectionCappingAnnulusProductDiffeomorph q).trans
      (X.innerTwoModelDiffeomorph hp hlin)⟩

namespace ElementaryPresentation
variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem fillingProductCarrier_linearize (E : ElementaryPresentation (NoCuts.carrier Q))
    (hT : TorusMappingClassLinear) (j : Fin E.toTorus.pairing.count) :
    fillingProductCarrier (E.linearize hT) j = fillingProductCarrier E j := rfl

end ElementaryPresentation
end GC.Seifert

namespace GC.Seifert

def outerFillingSignedModel (q : ℤ) :
    PartialDiffeomorph signedCollarModel (𝓡∂ 3) (Torus × ℝ)
      ElementaryPresentation.outerCappingProductSet.{u} ∞ :=
  (chartPolar 1).symm.trans (normalOuterTubeAtlas.{u} q 0)

theorem outerFillingSignedModel_source (q : ℤ) :
    (outerFillingSignedModel.{u} q).source = {x : Torus × ℝ | -2 < x.2 ∧ x.2 < 1 / 2} := by
  ext x
  change (-2 < x.2 ∧ (chartPolar 1).symm x ∈ (normalOuterTubeAtlas q 0).source) ↔ _
  rw [normalOuterTubeAtlas_source]
  change (-2 < x.2 ∧ ‖(seamRadius 1 x.2 / 3) • (x.1.1 : ℂ)‖ < 5 / 4) ↔ _
  constructor
  · rintro ⟨hx, hy⟩
    have hr := seamRadius_pos 1 hx
    rw [norm_smul, Circle.norm_coe, mul_one,
      Real.norm_of_nonneg (div_nonneg hr.le (by norm_num))] at hy
    have hs : seamRadius 1 x.2 / 3 = 1 + x.2 / 2 := by
      simp [seamRadius, Real.rpow_one]
    exact ⟨hx, by rw [hs] at hy; linarith⟩
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    have hr := seamRadius_pos 1 hx
    rw [norm_smul, Circle.norm_coe, mul_one,
      Real.norm_of_nonneg (div_nonneg hr.le (by norm_num))]
    have hs : seamRadius 1 x.2 / 3 = 1 + x.2 / 2 := by
      simp [seamRadius, Real.rpow_one]
    rw [hs]
    linarith

theorem outerFillingSignedModel_apply_val (q : ℤ) (t : Torus) (s : ℝ)
    (hs0 : -2 < s) (hs1 : s < 1 / 2) :
    (outerFillingSignedModel.{u} q (t, s)).val =
      (ULift.up (normalOuterTubeMap q 0 ((1 + s / 2) • (t.1 : ℂ), t.2)).1,
        (normalOuterTubeMap q 0 ((1 + s / 2) • (t.1 : ℂ), t.2)).2) := by
  have hr : 0 < 1 + s / 2 := by linarith
  have hn : ‖(1 + s / 2) • (t.1 : ℂ)‖ < 5 / 4 := by
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le]
    linarith
  have hs : seamRadius 1 s / 3 = 1 + s / 2 := by
    simp [seamRadius, Real.rpow_one]
  change (normalOuterTubeAtlas q 0 ((seamRadius 1 s / 3) • (t.1 : ℂ), t.2)).val = _
  rw [hs]
  exact normalOuterTubeAtlas_apply_val q 0 _ hn

end GC.Seifert

namespace GC.Seifert.ElementaryPresentation

def outerHostSource : TopologicalSpace.Opens (planarSet.{u} 3 × Circle) :=
  ⟨{x | ‖x.1.val.down‖ < 3},
    isOpen_lt ((continuous_uliftDown.comp continuous_subtype_val).comp
      continuous_fst).norm continuous_const⟩

def outerHostTarget : TopologicalSpace.Opens outerCappingProductSet.{u} :=
  ⟨{y | y.val.1.down ≠ 0 ∧ ‖y.val.1.down⁻¹ + (3 / 2 : ℂ)‖ < 3}, by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hc : Continuous (fun z : outerCappingProductSet.{u} => z.val.1.down) :=
      continuous_uliftDown.comp (continuous_fst.comp continuous_subtype_val)
    have hn : IsOpen {z : outerCappingProductSet.{u} | z.val.1.down ≠ 0} :=
      isOpen_ne_fun hc continuous_const
    have hnorm : ContinuousAt
        (fun z : outerCappingProductSet.{u} => ‖z.val.1.down⁻¹ + (3 / 2 : ℂ)‖) y :=
      ((hc.continuousAt.inv₀ hy.1).add continuousAt_const).norm
    exact Filter.inter_mem (hn.mem_nhds hy.1)
      (hnorm.preimage_mem_nhds (Iio_mem_nhds hy.2))⟩

theorem outerCappingHostProduct_mem_hostTarget (q : ℤ)
    (x : planarSet.{u} 3 × Circle) (hx : ‖x.1.val.down‖ < 3) :
    outerCappingHostProduct q x ∈ outerHostTarget.{u} := by
  change (x.1.val.down - (3 / 2 : ℂ))⁻¹ ≠ 0 ∧
    ‖((x.1.val.down - (3 / 2 : ℂ))⁻¹)⁻¹ + (3 / 2 : ℂ)‖ < 3
  exact ⟨inv_ne_zero (cappingOuterHost_denominator x.1), by
    rw [inv_inv, sub_add_cancel]; exact hx⟩

theorem outerCappingDiscProduct_not_mem_hostTarget (q : ℤ) (x : UnitDisc.{u} × Circle) :
    outerCappingDiscProduct q x ∉ outerHostTarget.{u} := by
  intro hx
  have hx0 : x.1.down.val ≠ 0 := by
    intro h
    have hz := hx.1
    change x.1.down.val / (3 - (3 / 2 : ℂ) * x.1.down.val) ≠ 0 at hz
    rw [h, zero_div] at hz
    exact hz rfl
  have he : (x.1.down.val / (3 - (3 / 2 : ℂ) * x.1.down.val))⁻¹ +
      (3 / 2 : ℂ) = 3 / x.1.down.val := by
    rw [inv_div]
    field_simp
    ring
  have hn : ‖x.1.down.val‖ ≤ 1 := by
    have h := x.1.down.property
    change ‖x.1.down.val‖ ^ 2 ≤ 1 at h
    nlinarith [norm_nonneg x.1.down.val]
  have hlt := hx.2
  change ‖(x.1.down.val / (3 - (3 / 2 : ℂ) * x.1.down.val))⁻¹ +
    (3 / 2 : ℂ)‖ < 3 at hlt
  rw [he, norm_div, Complex.norm_ofNat] at hlt
  have hge : 3 ≤ 3 / ‖x.1.down.val‖ :=
    (le_div_iff₀ (norm_pos_iff.mpr hx0)).mpr (by nlinarith)
  exact not_lt_of_ge hge hlt

theorem outerCappingHostProduct_injective (q : ℤ) :
    Function.Injective (outerCappingHostProduct.{u} q) := by
  intro x y h
  have he := outerCappingProductDiffeomorph.injective h
  have hb : x.1 = y.1 := outerCappingHost_injective (congrArg Prod.fst he)
  apply Prod.ext hb
  have hv := congrArg Prod.snd he
  change outerCappingHostPhase q x.1 * x.2 = outerCappingHostPhase q y.1 * y.2 at hv
  rw [hb] at hv
  exact mul_left_cancel hv

def outerHostMap (q : ℤ) (x : outerHostSource.{u}) : outerHostTarget.{u} :=
  ⟨outerCappingHostProduct q x.val, outerCappingHostProduct_mem_hostTarget q x.val x.property⟩

theorem outerHostMap_bijective (q : ℤ) : Function.Bijective (outerHostMap.{u} q) := by
  constructor
  · intro x y h
    exact Subtype.ext (outerCappingHostProduct_injective q (congrArg Subtype.val h))
  · intro y
    rcases outerCappingProduct_cover q y.val with ⟨x, hx⟩ | ⟨x, hx⟩
    · have hn : ‖x.1.val.down‖ < 3 := by
        have ht := y.property.2
        rw [← hx] at ht
        change ‖((x.1.val.down - (3 / 2 : ℂ))⁻¹)⁻¹ + (3 / 2 : ℂ)‖ < 3 at ht
        rwa [inv_inv, sub_add_cancel] at ht
      exact ⟨⟨x, hn⟩, Subtype.ext hx⟩
    · exact False.elim (outerCappingDiscProduct_not_mem_hostTarget q x (hx.symm ▸ y.property))

def outerHostEquiv (q : ℤ) : outerHostSource.{u} ≃ outerHostTarget.{u} :=
  Equiv.ofBijective (outerHostMap q) (outerHostMap_bijective q)

theorem outerHostEquiv_inverse_base (q : ℤ) (y : outerHostTarget.{u}) :
    (outerHostEquiv q).symm y |>.val.1.val.down = y.val.val.1.down⁻¹ + (3 / 2 : ℂ) := by
  have h := congrArg (fun x : outerHostTarget.{u} => x.val.val.1.down)
    ((outerHostEquiv q).apply_symm_apply y)
  change (((outerHostEquiv q).symm y).val.1.val.down - (3 / 2 : ℂ))⁻¹ =
    y.val.val.1.down at h
  rw [← h, inv_inv, sub_add_cancel]

theorem outerHostEquiv_inverse_fibre (q : ℤ) (y : outerHostTarget.{u}) :
    ((outerHostEquiv q).symm y).val.2 =
      (outerCappingHostPhase q ((outerHostEquiv q).symm y).val.1)⁻¹ * y.val.val.2 := by
  have h := congrArg (fun x : outerHostTarget.{u} => x.val.val.2)
    ((outerHostEquiv q).apply_symm_apply y)
  change outerCappingHostPhase q ((outerHostEquiv q).symm y).val.1 *
    ((outerHostEquiv q).symm y).val.2 = y.val.val.2 at h
  rw [← h, inv_mul_cancel_left]

def outerHostDiffeomorph (q : ℤ) :
    outerHostSource.{u} ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ outerHostTarget.{u} where
  toEquiv := outerHostEquiv q
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff outerHostTarget _).mp
    exact (outerCappingHostProduct_smooth q).comp contMDiff_subtype_val
  contMDiff_invFun := by
    have hb : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞
        (fun y : outerHostTarget.{u} => y.val.val.1.down⁻¹ + (3 / 2 : ℂ)) := by
      have hc : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞
          (fun y : outerHostTarget.{u} => y.val.val.1.down) :=
        contMDiff_planeLift_down.comp
          ((contMDiff_fst.comp outerCappingProductAtlas.contMDiff_subtype_val).comp
            contMDiff_subtype_val)
      intro y
      exact (((contDiffAt_inv ℂ y.property.1).restrict_scalars ℝ).contMDiffAt.comp y
        hc.contMDiffAt).add
        contMDiffAt_const
    have hbase : ContMDiff (𝓡∂ 3) (𝓡∂ 2) ∞
        (fun y : outerHostTarget.{u} => ((outerHostEquiv q).symm y).val.1) := by
      apply ((planarAtlas 3).contMDiff_iff_subtype_val _).mpr
      have he : (fun y : outerHostTarget.{u} =>
          ((outerHostEquiv q).symm y).val.1.val) =
        (fun y => ULift.up (y.val.val.1.down⁻¹ + (3 / 2 : ℂ))) := by
        funext y
        exact ULift.ext (outerHostEquiv_inverse_base q y)
      change ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞
        (fun y : outerHostTarget.{u} => ((outerHostEquiv q).symm y).val.1.val)
      rw [he]
      exact contMDiff_planeLift_up.comp hb
    have hfibre : ContMDiff (𝓡∂ 3) (𝓡 1) ∞
        (fun y : outerHostTarget.{u} => ((outerHostEquiv q).symm y).val.2) := by
      have he : (fun y : outerHostTarget.{u} => ((outerHostEquiv q).symm y).val.2) =
        (fun y => (outerCappingHostPhase q ((outerHostEquiv q).symm y).val.1)⁻¹ *
          y.val.val.2) := funext (outerHostEquiv_inverse_fibre q)
      rw [he]
      exact (((outerCappingHostPhase_smooth q).comp hbase).inv).mul
        ((contMDiff_snd.comp outerCappingProductAtlas.contMDiff_subtype_val).comp
          contMDiff_subtype_val)
    apply (ContMDiff.subtypeVal_comp_iff outerHostSource _).mp
    exact hbase.prodMk hfibre

end GC.Seifert.ElementaryPresentation

namespace GC.Seifert

def outerFillingCapNormalize (x : solidSet.{u}) : ℂ × Circle :=
  (x.val.1.down / 3, x.val.2)

theorem outerFillingCapNormalize_norm (x : solidSet.{u}) :
    ‖(outerFillingCapNormalize x).1‖ ≤ 1 := by
  have hx := (mem_discSet_iff x.val.1).mp x.property
  change ‖x.val.1.down‖ ≤ 3 at hx
  rw [outerFillingCapNormalize, norm_div, Complex.norm_ofNat]
  exact (div_le_one₀ (by norm_num)).mpr hx

theorem outerFillingCapNormalize_smooth :
    ContMDiff (𝓡∂ 3) PlaneCircleModel ∞ outerFillingCapNormalize.{u} :=
  ((contDiff_id.div_const (3 : ℂ)).contMDiff.comp
    (contMDiff_planeLift_down.comp
      (contMDiff_fst.comp solidAtlas.contMDiff_subtype_val))).prodMk
        (contMDiff_snd.comp solidAtlas.contMDiff_subtype_val)

def outerFillingCapModel (q : ℤ) (x : solidSet.{u}) :
    ElementaryPresentation.outerCappingProductSet.{u} :=
  normalOuterTubeAtlas q 0 (outerFillingCapNormalize x)

theorem outerFillingCapModel_smooth (q : ℤ) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (outerFillingCapModel.{u} q) := by
  intro x
  have hx : outerFillingCapNormalize x ∈ (normalOuterTubeAtlas q 0).source := by
    rw [normalOuterTubeAtlas_source]
    exact lt_of_le_of_lt (outerFillingCapNormalize_norm x) (by norm_num)
  exact ((normalOuterTubeAtlas q 0).contMDiffOn.contMDiffAt
    ((normalOuterTubeAtlas q 0).open_source.mem_nhds hx)).comp x
      outerFillingCapNormalize_smooth.contMDiffAt

def outerFillingCutModel (q : ℤ) : ConeFilling.FilledCut.{u} →
    ElementaryPresentation.outerCappingProductSet.{u} :=
  Sum.elim
    (ElementaryPresentation.outerCappingHostProduct q ∘ (productDiffeomorph 3).symm)
    (outerFillingCapModel q)

theorem outerFillingCutModel_smooth (q : ℤ) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (outerFillingCutModel.{u} q) :=
  ((ElementaryPresentation.outerCappingHostProduct_smooth q).comp
    (productDiffeomorph 3).symm.contMDiff).sumElim (outerFillingCapModel_smooth q)

theorem outerFillingCapNormalize_injective :
    Function.Injective outerFillingCapNormalize.{u} := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    have he : x.val.1.down / 3 = y.val.1.down / 3 := congrArg Prod.fst h
    exact (div_left_inj' (by norm_num : (3 : ℂ) ≠ 0)).mp he
  · exact congrArg (fun z : ℂ × Circle => z.2) h

theorem outerFillingCapModel_injective (q : ℤ) :
    Function.Injective (outerFillingCapModel.{u} q) := by
  intro x y h
  apply outerFillingCapNormalize_injective
  apply (normalOuterTubeAtlas q 0).injOn ?_ ?_ h
  · rw [normalOuterTubeAtlas_source]
    exact lt_of_le_of_lt (outerFillingCapNormalize_norm x) (by norm_num)
  · rw [normalOuterTubeAtlas_source]
    exact lt_of_le_of_lt (outerFillingCapNormalize_norm y) (by norm_num)

theorem outerFillingCapModel_apply_val (q : ℤ) (x : solidSet.{u}) :
    (outerFillingCapModel q x).val =
      (ULift.up (normalOuterTubeMap q 0 (outerFillingCapNormalize x)).1,
        (normalOuterTubeMap q 0 (outerFillingCapNormalize x)).2) :=
  normalOuterTubeAtlas_apply_val q 0 _
    (lt_of_le_of_lt (outerFillingCapNormalize_norm x) (by norm_num))

def outerFillingCapUnit (x : solidSet.{u}) : UnitDisc.{0} :=
  ULift.up ⟨(outerFillingCapNormalize x).1, by
    change ‖(outerFillingCapNormalize x).1‖ ^ 2 ≤ 1
    have hx := outerFillingCapNormalize_norm x
    nlinarith [norm_nonneg (outerFillingCapNormalize x).1]⟩

def outerFillingCapReparam (x : solidSet.{u}) : UnitDisc.{u} :=
  ULift.up (normalOuterDiscReparamDiffeomorph (outerFillingCapUnit x)).down

theorem outerFillingCapModel_raw (q : ℤ) (x : solidSet.{u}) :
    outerFillingCapModel q x = ElementaryPresentation.outerCappingDiscProduct q
      (outerFillingCapReparam x, x.val.2) := by
  apply Subtype.ext
  rw [outerFillingCapModel_apply_val]
  apply Prod.ext
  · apply ULift.ext
    change (normalOuterTubeMap q 0 (outerFillingCapNormalize x)).1 =
      ElementaryPresentation.cappingOuterDiscMap
        (normalOuterDiscReparamDiffeomorph (outerFillingCapUnit x))
    simp only [normalOuterTubeMap, solidBasisExtension, neg_zero, zpow_zero,
      Circle.coe_one, mul_one]
    exact (normalOuterDiscReparamDiffeomorph_map (outerFillingCapUnit x)).symm
  · change (normalOuterTubeMap q 0 (outerFillingCapNormalize x)).2 =
      ElementaryPresentation.outerCappingCapPhase q
        (normalOuterDiscReparamDiffeomorph (outerFillingCapUnit x)) * x.val.2
    simp only [normalOuterTubeMap, solidBasisExtension, neg_zero, zpow_zero,
      Circle.coe_one, mul_one]
    rw [normalOuterDiscReparamDiffeomorph_phase]
    rfl

def outerFillingCapOfUnit (z : UnitDisc.{0}) (v : Circle) : solidSet.{u} :=
  ⟨(ULift.up ((3 : ℂ) * z.down.val), v), by
    change sqDist 0 3 ((3 : ℂ) * z.down.val) ≤ 0
    apply (mem_discSet_iff (ULift.up ((3 : ℂ) * z.down.val) : PlaneLift.{u})).mpr
    rw [norm_mul, Complex.norm_ofNat]
    have hz := z.down.property
    change ‖z.down.val‖ ^ 2 ≤ 1 at hz
    nlinarith [norm_nonneg z.down.val]⟩

theorem outerFillingCapUnit_ofUnit (z : UnitDisc.{0}) (v : Circle) :
    outerFillingCapUnit (outerFillingCapOfUnit.{u} z v) = z := by
  apply ULift.ext
  apply Subtype.ext
  change ((3 : ℂ) * z.down.val) / 3 = z.down.val
  ring

theorem outerFillingCapReparam_surjective :
    Function.Surjective outerFillingCapReparam.{u} := by
  intro z
  let z0 : UnitDisc.{0} := ULift.up z.down
  obtain ⟨w, hw⟩ := normalOuterDiscReparamDiffeomorph.surjective z0
  change normalOuterDiscReparamDiffeomorph w = z0 at hw
  refine ⟨outerFillingCapOfUnit.{u} w 1, ?_⟩
  unfold outerFillingCapReparam
  rw [outerFillingCapUnit_ofUnit, hw]

theorem outerFillingCutModel_surjective (q : ℤ) :
    Function.Surjective (outerFillingCutModel.{u} q) := by
  intro y
  rcases ElementaryPresentation.outerCappingProduct_cover q y with ⟨x, hx⟩ | ⟨x, hx⟩
  · refine ⟨Sum.inl (productDiffeomorph 3 x), ?_⟩
    change ElementaryPresentation.outerCappingHostProduct q
      ((productDiffeomorph 3).symm (productDiffeomorph 3 x)) = y
    rwa [Diffeomorph.symm_apply_apply]
  · let z0 : UnitDisc.{0} := ULift.up x.1.down
    let w := normalOuterDiscReparamDiffeomorph.symm z0
    refine ⟨Sum.inr (outerFillingCapOfUnit.{u} w x.2), ?_⟩
    change outerFillingCapModel q (outerFillingCapOfUnit.{u} w x.2) = y
    rw [outerFillingCapModel_raw]
    have he : outerFillingCapReparam (outerFillingCapOfUnit.{u} w x.2) = x.1 := by
      unfold outerFillingCapReparam
      rw [outerFillingCapUnit_ofUnit, Diffeomorph.apply_symm_apply]
    rw [he]
    exact hx

theorem outerFillingCapUnit_collar_zero (t : Torus) :
    outerFillingCapUnit (solidCollar.{u} 1 (t, halfZero)) =
      ElementaryPresentation.fillingDiscBoundary t.1 := by
  apply ULift.ext
  apply Subtype.ext
  change (solidCollar.{u} 1 (t, halfZero)).val.1.down / 3 = t.1
  rw [solidCollar_zero_val]
  change ((3 : ℝ) • (t.1 : ℂ)) / 3 = t.1
  rw [Complex.real_smul]
  norm_num

theorem outerFillingCapReparam_collar_zero (t : Torus) :
    outerFillingCapReparam (solidCollar.{u} 1 (t, halfZero)) =
      ElementaryPresentation.outerCappingDiscBoundary t.1 := by
  unfold outerFillingCapReparam
  rw [outerFillingCapUnit_collar_zero, normalOuterDiscReparamDiffeomorph_boundary]
  rfl

theorem sectionFilling_matching_pair (q : ℤ) (t : Torus) :
    (Merge.sectionFilling q).matching t = (t.1⁻¹, t.1 ^ (-q) * t.2) := by
  apply Prod.ext <;>
    simp [ConeFilling.matching_apply, ConeFilling.matchingMatrix, ConeFilling.reflectMatrix,
      ConeFilling.chartMatrix, Merge.sectionFilling, linearTorusMap]

theorem outerFillingCutModel_boundary (q : ℤ) (t : Torus) :
    outerFillingCutModel q (Sum.inr (solidCollar.{u} 1 (t, halfZero))) =
      outerFillingCutModel q (Sum.inl (productDiffeomorph 3
        (planarCollar 3 (Or.inr rfl) 0 (((Merge.sectionFilling q).matching t).1, halfZero),
          ((Merge.sectionFilling q).matching t).2))) := by
  change outerFillingCapModel q (solidCollar 1 (t, halfZero)) = _
  rw [outerFillingCapModel_raw, outerFillingCapReparam_collar_zero]
  change ElementaryPresentation.outerCappingDiscProduct q
    (ElementaryPresentation.outerCappingDiscBoundary t.1, t.2) =
      ElementaryPresentation.outerCappingHostProduct q
        ((productDiffeomorph 3).symm (productDiffeomorph 3 _))
  rw [Diffeomorph.symm_apply_apply, sectionFilling_matching_pair]
  exact (ElementaryPresentation.outerCappingProduct_matching q t.1 t.2).symm

theorem outerFillingCutModel_cross (q : ℤ) (a : productSet.{u} 3) (b : solidSet.{u})
    (he : outerFillingCutModel q (Sum.inl a) = outerFillingCutModel q (Sum.inr b)) :
    ∃ t : Torus, b = solidCollar 1 (t, halfZero) ∧
      a = productDiffeomorph 3
        (planarCollar 3 (Or.inr rfl) 0 (((Merge.sectionFilling q).matching t).1, halfZero),
          ((Merge.sectionFilling q).matching t).2) := by
  let z := (outerFillingCapReparam b).down.val
  let τ := unitOf z
  have hh := congrArg (fun y : ElementaryPresentation.outerCappingProductSet.{u} =>
    y.val.1.down) he
  change (((productDiffeomorph 3).symm a).1.val.down - (3 / 2 : ℂ))⁻¹ =
    (outerFillingCapModel q b).val.1.down at hh
  rw [outerFillingCapModel_raw] at hh
  change (((productDiffeomorph 3).symm a).1.val.down - (3 / 2 : ℂ))⁻¹ =
    z / (3 - (3 / 2 : ℂ) * z) at hh
  have hz : ‖z‖ ≤ 1 := by
    have h := (outerFillingCapReparam b).down.property
    change ‖z‖ ^ 2 ≤ 1 at h
    nlinarith [norm_nonneg z]
  have ha := ((mem_planarSet_iff (Or.inr rfl) _).mp
    (((productDiffeomorph 3).symm a).1.property))
  have hn := (ElementaryPresentation.outerCapping_overlap _ z ha hz hh).1
  have hτ : (τ : ℂ) = z := by
    have h := norm_smul_unitOf z
    rw [hn, one_smul] at h
    exact h
  have hR : normalOuterDiscReparamDiffeomorph (outerFillingCapUnit b) =
      ElementaryPresentation.fillingDiscBoundary τ := by
    apply ULift.ext
    apply Subtype.ext
    exact hτ.symm
  have hb0 := normalOuterDiscReparamDiffeomorph.injective
    (hR.trans (normalOuterDiscReparamDiffeomorph_boundary τ).symm)
  have hb : b = solidCollar 1 ((τ, b.val.2), halfZero) := by
    apply Subtype.ext
    rw [solidCollar_zero_val]
    apply Prod.ext
    · apply ULift.ext
      have h := congrArg (fun y : UnitDisc.{0} => y.down.val) hb0
      change b.val.1.down / 3 = τ at h
      rw [Complex.real_smul]
      calc
        b.val.1.down = (τ : ℂ) * 3 :=
          ((eq_div_iff (by norm_num : (3 : ℂ) ≠ 0)).mp h.symm).symm
        _ = 3 * (τ : ℂ) := mul_comm _ _
    · rfl
  refine ⟨(τ, b.val.2), hb, ?_⟩
  apply (productDiffeomorph 3).symm.injective
  apply ElementaryPresentation.outerCappingHostProduct_injective q
  have h := outerFillingCutModel_boundary.{u} q (τ, b.val.2)
  rw [← hb] at h
  exact he.trans h

end GC.Seifert

namespace GC.Seifert
variable {W : CompactCarrier.{u}} {q : ℤ} {B : SeifertBlock W (selectedNormalData q)}

theorem NormalFillingTrivializations.modelOuter_rightCollar (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))
    (t : Torus) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : r < X.hostDepth) :
    X.cutDiffeomorph (Sum.inl (productDiffeomorph 3
      (planarCollar 3 (Or.inr rfl) 0 (((Merge.sectionFilling q).matching t).1,
        halfPoint r hr0), ((Merge.sectionFilling q).matching t).2))) =
      B.presentation.pairing.rightCollar (B.seam (normalFillingIndex q))
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q))
          (linearTorusMap X.basis t), halfPoint r hr0) := by
  let τ := (Merge.sectionFilling q).matching t
  have hp : (τ, halfPoint r hr0) ∈ halfCollarSource := hr1
  have h := congrArg Subtype.val (X.host_collar (B.port (.inr (normalFillingIndex q)))
    (τ, halfPoint r hr0) hp hr)
  rw [TorusPresentation.pieceCollar_apply _ _ _ hp, B.filled_port, hport] at h
  change B.presentation.pairing.rightCollar (B.seam (normalFillingIndex q))
    (τ, halfPoint r hr0) = _ at h
  rw [X.cutDiffeomorph_inl, Diffeomorph.symm_apply_apply]
  rw [X.matching_basis hlin]
  exact h.symm

theorem NormalFillingTrivializations.modelOuter_leftParam (X : NormalFillingTrivializations B)
    (t : Torus) : X.cutDiffeomorph (Sum.inr (solidCollar 1 (t, halfZero))) =
      (B.presentation.pairing.leftParam (B.seam (normalFillingIndex q))
        (linearTorusMap X.basis t)).val := by
  rw [← B.presentation.pairing.left_zero]
  exact X.model_leftCollar t 0 (by norm_num) (by norm_num) X.solidDepth_pos

theorem NormalFillingTrivializations.modelOuter_rightParam (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))
    (t : Torus) : X.cutDiffeomorph (Sum.inl (productDiffeomorph 3
      (planarCollar 3 (Or.inr rfl) 0 (((Merge.sectionFilling q).matching t).1, halfZero),
        ((Merge.sectionFilling q).matching t).2))) =
      (B.presentation.pairing.rightParam (B.seam (normalFillingIndex q))
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q))
          (linearTorusMap X.basis t))).val := by
  rw [← B.presentation.pairing.right_zero]
  exact X.modelOuter_rightCollar hport hlin t 0 (by norm_num) (by norm_num) X.hostDepth_pos

theorem SeifertBlock.normalSeam_eq (k : Fin B.presentation.pairing.count) :
    k = B.seam (normalFillingIndex q) := by
  have hm : B.seam.symm k = normalFillingIndex q := by
    apply Fin.ext
    have h := (B.seam.symm k).isLt
    change (B.seam.symm k).val < 1 at h
    change (B.seam.symm k).val = 0
    omega
  exact (B.seam.apply_symm_apply k).symm.trans (congrArg B.seam hm)

def NormalFillingTrivializations.outerCutMap (X : NormalFillingTrivializations B) :
    B.presentation.cutCarrier.Carrier → ElementaryPresentation.outerCappingProductSet.{u} :=
  outerFillingCutModel q ∘ X.cutDiffeomorph.symm

theorem NormalFillingTrivializations.outerCutMap_smooth (X : NormalFillingTrivializations B) :
    ContMDiff B.presentation.cutCarrier.model (𝓡∂ 3) ∞ X.outerCutMap :=
  (outerFillingCutModel_smooth q).comp X.cutDiffeomorph.symm.contMDiff

theorem NormalFillingTrivializations.outerCutMap_surjective
    (X : NormalFillingTrivializations B) : Function.Surjective X.outerCutMap :=
  (outerFillingCutModel_surjective q).comp X.cutDiffeomorph.symm.surjective

theorem NormalFillingTrivializations.outerCutMap_boundary
    (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))
    (k : Fin B.presentation.pairing.count) (t : Torus) :
    X.outerCutMap (B.presentation.pairing.leftParam k t).val =
      X.outerCutMap (B.presentation.pairing.rightParam k
        (B.presentation.pairing.matching k t)).val := by
  obtain rfl := B.normalSeam_eq k
  let τ := (linearTorusDiffeomorph X.basis).symm t
  have ht : linearTorusMap X.basis τ = t :=
    (linearTorusDiffeomorph X.basis).apply_symm_apply t
  have hl := X.modelOuter_leftParam τ
  have hr := X.modelOuter_rightParam hport hlin τ
  rw [ht] at hl hr
  rw [← hl, ← hr]
  simp only [outerCutMap, Function.comp_apply, Diffeomorph.symm_apply_apply]
  exact outerFillingCutModel_boundary q τ

theorem NormalFillingTrivializations.outerCutMap_rel
    (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))
    (x y : B.presentation.cutCarrier.Carrier) :
    B.presentation.pairing.gluing.rel x y ↔ X.outerCutMap x = X.outerCutMap y := by
  constructor
  · rw [GC.Seifert.TorusPairing.rel_iff_params]
    rintro (rfl | ⟨k, t, h | h⟩)
    · rfl
    · rcases h with ⟨rfl, rfl⟩
      exact X.outerCutMap_boundary hport hlin k t
    · rcases h with ⟨rfl, rfl⟩
      exact (X.outerCutMap_boundary hport hlin k t).symm
  · intro h
    obtain ⟨x, rfl⟩ := X.cutDiffeomorph.surjective x
    obtain ⟨y, rfl⟩ := X.cutDiffeomorph.surjective y
    change outerFillingCutModel q (X.cutDiffeomorph.symm (X.cutDiffeomorph x)) =
      outerFillingCutModel q (X.cutDiffeomorph.symm (X.cutDiffeomorph y)) at h
    rw [Diffeomorph.symm_apply_apply, Diffeomorph.symm_apply_apply] at h
    rw [GC.Seifert.TorusPairing.rel_iff_params]
    rcases x with x | x <;> rcases y with y | y
    · left
      change ElementaryPresentation.outerCappingHostProduct q
        ((productDiffeomorph 3).symm x) = ElementaryPresentation.outerCappingHostProduct q
          ((productDiffeomorph 3).symm y) at h
      have he := (productDiffeomorph 3).symm.injective
        (ElementaryPresentation.outerCappingHostProduct_injective q h)
      exact congrArg X.cutDiffeomorph (congrArg Sum.inl he)
    · right
      obtain ⟨t, hy, hx⟩ := outerFillingCutModel_cross q x y h
      refine ⟨B.seam (normalFillingIndex q), linearTorusMap X.basis t, Or.inr ⟨?_, ?_⟩⟩
      · rw [hy]
        exact X.modelOuter_leftParam t
      · rw [hx]
        exact X.modelOuter_rightParam hport hlin t
    · right
      obtain ⟨t, hx, hy⟩ := outerFillingCutModel_cross q y x h.symm
      refine ⟨B.seam (normalFillingIndex q), linearTorusMap X.basis t, Or.inl ⟨?_, ?_⟩⟩
      · rw [hx]
        exact X.modelOuter_leftParam t
      · rw [hy]
        exact X.modelOuter_rightParam hport hlin t
    · left
      have he := outerFillingCapModel_injective q h
      exact congrArg X.cutDiffeomorph (congrArg Sum.inr he)

end GC.Seifert

namespace GC.Seifert.TorusPresentation
variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
variable {N : Type*} [TopologicalSpace N] [T2Space N]

def descendCutMap (f : T.cutCarrier.Carrier → N)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ f x = f y) : W.Carrier → N :=
  fun x => Quotient.lift f (fun a b h => (hrel a b).mp h) (T.reconstruction.symm x)

omit [TopologicalSpace N] [T2Space N] in
theorem descendCutMap_cutMap (f : T.cutCarrier.Carrier → N)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ f x = f y)
    (x : T.cutCarrier.Carrier) : T.descendCutMap f hrel (T.cutMap x) = f x := by
  unfold descendCutMap cutMap
  rw [Homeomorph.symm_apply_apply]
  rfl

def cutModelHomeomorph (f : T.cutCarrier.Carrier → N) (hf : Continuous f)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ f x = f y)
    (hsur : Function.Surjective f) : W.Carrier ≃ₜ N := by
  let g := T.descendCutMap f hrel
  have hg : Continuous g :=
    (continuous_quot_lift _ hf).comp T.reconstruction.symm.continuous
  have hinj : Function.Injective g := by
    intro x y he
    obtain ⟨a, rfl⟩ := T.cutMap_surjective x
    obtain ⟨b, rfl⟩ := T.cutMap_surjective y
    change T.descendCutMap f hrel (T.cutMap a) =
      T.descendCutMap f hrel (T.cutMap b) at he
    rw [T.descendCutMap_cutMap, T.descendCutMap_cutMap] at he
    exact congrArg T.reconstruction (Quotient.sound' ((hrel a b).mpr he))
  have hsur' : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := hsur y
    exact ⟨T.cutMap a, T.descendCutMap_cutMap f hrel a⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hinj, hsur'⟩) hg

theorem cutModelHomeomorph_cutMap (f : T.cutCarrier.Carrier → N) (hf : Continuous f)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ f x = f y)
    (hsur : Function.Surjective f) (x : T.cutCarrier.Carrier) :
    T.cutModelHomeomorph f hf hrel hsur (T.cutMap x) = f x :=
  T.descendCutMap_cutMap f hrel x

end GC.Seifert.TorusPresentation

namespace GC.Seifert
variable {W : CompactCarrier.{u}} {q : ℤ} {B : SeifertBlock W (selectedNormalData q)}

def NormalFillingTrivializations.outerModelHomeomorph
    (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q))))) :
    W.Carrier ≃ₜ ElementaryPresentation.outerCappingProductSet.{u} :=
  B.presentation.cutModelHomeomorph X.outerCutMap X.outerCutMap_smooth.continuous
    (X.outerCutMap_rel hport hlin) X.outerCutMap_surjective

theorem NormalFillingTrivializations.outerModelHomeomorph_cutMap
    (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))
    (x : B.presentation.cutCarrier.Carrier) :
    X.outerModelHomeomorph hport hlin (B.presentation.cutMap x) = X.outerCutMap x :=
  B.presentation.cutModelHomeomorph_cutMap X.outerCutMap X.outerCutMap_smooth.continuous
    (X.outerCutMap_rel hport hlin) X.outerCutMap_surjective x

end GC.Seifert

namespace GC.Seifert

theorem outerFillingSignedModel_host (q : ℤ) (t : Torus) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1 / 2) :
    outerFillingSignedModel.{u} q (t, s) =
      ElementaryPresentation.outerCappingHostProduct q
        (planarCollar 3 (Or.inr rfl) 0 (((Merge.sectionFilling q).matching t).1,
          halfPoint s hs0.le), ((Merge.sectionFilling q).matching t).2) := by
  let y : ℂ × Circle := ((1 + s / 2) • (t.1 : ℂ), t.2)
  have hr : 0 < 1 + s / 2 := by linarith
  have hn : ‖y.1‖ = 1 + s / 2 := by
    change ‖(1 + s / 2 : ℝ) • (t.1 : ℂ)‖ = _
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le]
  have hy : 1 < ‖y.1‖ ∧ ‖y.1‖ < 5 / 4 := by rw [hn]; constructor <;> linarith
  let A := chartConventionUnit 1 q 0 1 (by simp)
  have ht : linearTorusMap A (unitOf y.1, y.2) = (Merge.sectionFilling q).matching t := by
    have hu : unitOf y.1 = t.1 := unitOf_smul hr t.1
    rw [hu]
    dsimp [y, A]
    simp [chartConventionUnit, PrimitiveSlope.val_unitOfDet, chartConventionMatrix,
      ConeFilling.matching_apply, ConeFilling.matchingMatrix, ConeFilling.reflectMatrix,
      ConeFilling.chartMatrix, Merge.sectionFilling]
  have hd : seamDepth 1 ‖3 * y.1‖ = s := by
    rw [norm_mul, Complex.norm_ofNat, hn]
    simp only [seamDepth, pow_one]
    ring
  have hp : (((Merge.sectionFilling q).matching t).1, halfPoint s hs0.le) ∈
      circleCollarSource := by change s < 1; linarith
  have he : seamModel (normalT2IntervalDatum q) 0 (0 : Fin 3) A y =
      ((planarCollar.{u} 3 (Or.inr rfl) 0
        (((Merge.sectionFilling q).matching t).1, halfPoint s hs0.le)).val.down,
          ((Merge.sectionFilling q).matching t).2) := by
    have hformula := seamModel_eq_planarCollarFormula (normalT2IntervalDatum q)
      (0 : Fin (normalT2IntervalDatum q).fillingCount)
      (⟨0, by change 0 < 3; decide⟩ : Fin (normalT2IntervalDatum q).k) A y
    simp only [normalT2IntervalDatum_fillingSlope, Int.natAbs_one] at hformula
    rw [ht, hd] at hformula
    exact hformula.trans (Prod.ext (planarCollar_apply_val.{u} (Or.inr rfl) 0 hp).symm rfl)
  have hmap := normalOuterTubeMap_seam q 0 1 (by simp) y hy
  change normalOuterTubeMap q 0 y = _ at hmap
  rw [he] at hmap
  apply Subtype.ext
  rw [outerFillingSignedModel_apply_val q t s (by linarith) hs1]
  change (ULift.up (normalOuterTubeMap q 0 y).1, (normalOuterTubeMap q 0 y).2) = _
  rw [hmap]
  rfl

end GC.Seifert

namespace GC.Seifert

theorem outerFillingSignedModel_cap (q : ℤ) (t : Torus) (s : ℝ)
    (hs0 : -1 / 2 < s) (hs1 : s ≤ 0) :
    outerFillingSignedModel.{u} q (t, s) =
      outerFillingCapModel q (solidCollar 1 (t, halfPoint (-s) (neg_nonneg.mpr hs1))) := by
  have hp : (t, halfPoint (-s) (neg_nonneg.mpr hs1)) ∈ halfCollarSource := by
    change -s < 1
    linarith
  have he : outerFillingCapNormalize
      (solidCollar.{u} 1 (t, halfPoint (-s) (neg_nonneg.mpr hs1))) =
      ((seamRadius 1 s / 3) • (t.1 : ℂ), t.2) := by
    unfold outerFillingCapNormalize
    rw [solidCollar_apply_val 1 hp]
    apply Prod.ext
    · change (seamRadius 1 (- -s) • (t.1 : ℂ)) / 3 = _
      rw [neg_neg, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    · rfl
  change normalOuterTubeAtlas q 0 ((seamRadius 1 s / 3) • (t.1 : ℂ), t.2) =
    normalOuterTubeAtlas q 0 (outerFillingCapNormalize _)
  rw [he]

end GC.Seifert

namespace GC.Seifert
variable {W : CompactCarrier.{u}} {q : ℤ} {B : SeifertBlock W (selectedNormalData q)}

def NormalFillingTrivializations.outerGermDepth (X : NormalFillingTrivializations B) : ℝ :=
  min (1 / 2) (min X.hostDepth X.solidDepth)

theorem NormalFillingTrivializations.outerGermDepth_pos (X : NormalFillingTrivializations B) :
    0 < X.outerGermDepth :=
  lt_min (by norm_num) (lt_min X.hostDepth_pos X.solidDepth_pos)

theorem NormalFillingTrivializations.outerModelHomeomorph_seam
    (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))
    (t : Torus) (s : ℝ) (hs : |s| < X.outerGermDepth) :
    X.outerModelHomeomorph hport hlin
      (B.presentation.seam (B.seam (normalFillingIndex q)) (linearTorusMap X.basis t, s)) =
        outerFillingSignedModel q (t, s) := by
  have hs' := abs_lt.mp hs
  have hhalf := min_le_left (1 / 2 : ℝ) (min X.hostDepth X.solidDepth)
  have hhost := (min_le_right (1 / 2 : ℝ) (min X.hostDepth X.solidDepth)).trans
    (min_le_left X.hostDepth X.solidDepth)
  have hsolid := (min_le_right (1 / 2 : ℝ) (min X.hostDepth X.solidDepth)).trans
    (min_le_right X.hostDepth X.solidDepth)
  by_cases hs0 : 0 < s
  · have h1 : s < 1 := by exact lt_trans (lt_of_lt_of_le hs'.2 hhalf) (by norm_num)
    rw [B.presentation.seam_positive _ _ s hs0.le h1]
    change X.outerModelHomeomorph hport hlin
      (B.presentation.cutMap (B.presentation.pairing.rightCollar _ _)) = _
    rw [← X.modelOuter_rightCollar hport hlin t s hs0.le h1
      (lt_of_lt_of_le hs'.2 hhost), X.outerModelHomeomorph_cutMap]
    change outerFillingCutModel q (X.cutDiffeomorph.symm (X.cutDiffeomorph _)) = _
    rw [Diffeomorph.symm_apply_apply]
    change ElementaryPresentation.outerCappingHostProduct q
      ((productDiffeomorph 3).symm (productDiffeomorph 3 _)) = _
    rw [Diffeomorph.symm_apply_apply]
    exact (outerFillingSignedModel_host q t s hs0 (lt_of_lt_of_le hs'.2 hhalf)).symm
  · have hs0' := not_lt.mp hs0
    have hlow : -1 < s := by
      have h := neg_lt_neg (lt_of_lt_of_le (neg_lt.mpr hs'.1) hhalf)
      linarith
    have hr : -s < 1 := by linarith
    rw [B.presentation.seam_negative _ _ s hs0' hlow]
    change X.outerModelHomeomorph hport hlin
      (B.presentation.cutMap (B.presentation.pairing.leftCollar _ _)) = _
    rw [← X.model_leftCollar t (-s) (neg_nonneg.mpr hs0') hr
      (lt_of_lt_of_le (neg_lt.mpr hs'.1) hsolid), X.outerModelHomeomorph_cutMap]
    change outerFillingCutModel q (X.cutDiffeomorph.symm (X.cutDiffeomorph _)) = _
    rw [Diffeomorph.symm_apply_apply]
    change outerFillingCapModel q (solidCollar 1 (t, halfPoint (-s) _)) = _
    exact (outerFillingSignedModel_cap q t s
      (by have h := lt_of_lt_of_le (neg_lt.mpr hs'.1) hhalf; linarith) hs0').symm

end GC.Seifert

namespace GC.Seifert
variable {W : CompactCarrier.{u}} {q : ℤ} {B : SeifertBlock W (selectedNormalData q)}
variable (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))

def NormalFillingTrivializations.outerBasisParam :
    (Torus × ℝ) ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ) :=
  (linearTorusDiffeomorph X.basis).prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)

theorem NormalFillingTrivializations.outerGerm_nhds (t : Torus) :
    {p : Torus × ℝ | |p.2| < X.outerGermDepth} ∈ 𝓝 (t, 0) := by
  apply (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const).mem_nhds
  simpa using X.outerGermDepth_pos

theorem NormalFillingTrivializations.outerModelHomeomorph_seam_smooth (t : Torus) :
    ContMDiffAt signedCollarModel (𝓡∂ 3) ∞
      (X.outerModelHomeomorph hport hlin ∘
        B.presentation.seam (B.seam (normalFillingIndex q))) (t, 0) := by
  let e := X.outerBasisParam.symm
  have hx : e (t, 0) ∈ (outerFillingSignedModel.{u} q).source := by
    rw [outerFillingSignedModel_source]
    change -2 < (0 : ℝ) ∧ (0 : ℝ) < 1 / 2
    exact ⟨by norm_num, by norm_num⟩
  have h := ((outerFillingSignedModel.{u} q).contMDiffOn.contMDiffAt
    ((outerFillingSignedModel.{u} q).open_source.mem_nhds hx)).comp (t, 0) e.contMDiffAt
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [X.outerGerm_nhds t] with p hp
  have he := X.outerModelHomeomorph_seam hport hlin
    ((linearTorusDiffeomorph X.basis).symm p.1) p.2 hp
  have ht : linearTorusMap X.basis ((linearTorusDiffeomorph X.basis).symm p.1) = p.1 :=
    (linearTorusDiffeomorph X.basis).apply_symm_apply p.1
  rw [ht] at he
  exact he

end GC.Seifert

namespace GC.Seifert.TorusPresentation
variable {W : CompactCarrier.{u}} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace 3) N]

theorem contMDiff_of_cutMap_seams_half (T : TorusPresentation W) (f : W.Carrier → N)
    (hcut : ContMDiff T.cutCarrier.model (𝓡∂ 3) ∞ (f ∘ T.cutMap))
    (hseam : ∀ k t, ContMDiffAt signedCollarModel (𝓡∂ 3) ∞
      (f ∘ T.seam k) (t, 0)) : ContMDiff W.model (𝓡∂ 3) ∞ f := by
  intro w
  obtain ⟨x, rfl⟩ := T.cutMap_surjective w
  by_cases hx : T.cutCarrier.model.IsInteriorPoint x
  · let xi : T.cutCarrier.interior := ⟨x, hx⟩
    have hxi : ContMDiffAt T.cutCarrier.model (𝓡∂ 3) ∞
        (fun y => f (T.interiorDiffeomorph y).val) xi := by
      have h := hcut.comp (contMDiff_subtype_val (U := T.cutCarrier.interior))
      have he : (fun y => f (T.interiorDiffeomorph y).val) =
          (f ∘ T.cutMap) ∘ Subtype.val := by
        funext y
        rw [T.interior_map]
        rfl
      rw [he]
      exact h xi
    have hs := (T.interiorDiffeomorph.symm_apply_apply xi).symm ▸ hxi
    have hs := hs.comp (T.interiorDiffeomorph xi)
      T.interiorDiffeomorph.symm.contMDiffAt
    have he : (fun y => f (T.interiorDiffeomorph
        (T.interiorDiffeomorph.symm y)).val) = (fun y : T.interiorImage => f y.val) := by
      funext y
      rw [Diffeomorph.apply_symm_apply]
    change ContMDiffAt W.model (𝓡∂ 3) ∞
      (fun y => f (T.interiorDiffeomorph (T.interiorDiffeomorph.symm y)).val) _ at hs
    rw [he] at hs
    have hs' := contMDiffAt_subtype_iff.mp hs
    simpa [xi, T.interior_map, TorusPresentation.cutMap] using hs' 
  · have hb : x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier :=
      (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint x).mpr hx
    rw [T.cut_boundary_exhausted] at hb
    rcases hb with hb | hb
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
      have he : ∃ t, T.cutMap x = T.seam k (t, 0) := by
        rcases hk with hl | hr
        · refine ⟨(T.pairing.leftParam k).symm ⟨x, hl⟩, ?_⟩
          rw [T.seam_zero, Homeomorph.apply_symm_apply]
          rfl
        · refine ⟨(T.pairing.matching k).symm
            ((T.pairing.rightParam k).symm ⟨x, hr⟩), ?_⟩
          rw [T.seam_zero]
          change T.reconstruction (T.pairing.quotientMap x) = _
          rw [T.quotientMap_leftParam_eq_rightParam_matching,
            Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
      obtain ⟨t, ht⟩ := he
      rw [ht]
      exact smoothAt_of_partial_comp (T.seam k) f
        (by rw [T.seam_source]; exact ⟨by norm_num, by norm_num⟩) (hseam k t)
    · obtain ⟨r, t, ht⟩ := mem_iUnion.mp hb
      have ht' : T.cutMap x = T.external.collar r (t, halfZero) := by
        rw [← ht]
        exact T.marked_collar r (t, halfZero) (zero_mem_halfCollarSource t)
      rw [ht']
      apply smoothAt_of_partial_comp (T.external.collar r) f
        (by rw [T.external.source_eq]; exact zero_mem_halfCollarSource t)
      have h := hcut.comp_contMDiffOn (T.cutExternal.collar r).contMDiffOn
      have he : EqOn (f ∘ T.external.collar r)
          ((f ∘ T.cutMap) ∘ T.cutExternal.collar r) halfCollarSource := by
        intro p hp
        exact congrArg f (T.marked_collar r p hp).symm
      have h' := h.congr (fun p hp => he ((T.cutExternal.source_eq r) ▸ hp))
      rw [T.cutExternal.source_eq r] at h'
      exact h'.contMDiffAt ((T.external.source_eq r) ▸
        (T.external.collar r).open_source.mem_nhds
          ((T.external.source_eq r).symm ▸ zero_mem_halfCollarSource t))

end GC.Seifert.TorusPresentation

namespace GC.Seifert
variable {W : CompactCarrier.{u}} {q : ℤ} {B : SeifertBlock W (selectedNormalData q)}
variable (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))

theorem NormalFillingTrivializations.outerModelHomeomorph_smooth :
    ContMDiff W.model (𝓡∂ 3) ∞ (X.outerModelHomeomorph hport hlin) := by
  apply B.presentation.contMDiff_of_cutMap_seams_half
  · have he : (X.outerModelHomeomorph hport hlin ∘ B.presentation.cutMap) =
      X.outerCutMap := funext (X.outerModelHomeomorph_cutMap hport hlin)
    rw [he]
    exact X.outerCutMap_smooth
  · intro k t
    obtain rfl := B.normalSeam_eq k
    exact X.outerModelHomeomorph_seam_smooth hport hlin t

theorem NormalFillingTrivializations.outerModelHomeomorph_inverse_seam_smooth (t : Torus) :
    ContMDiffAt (𝓡∂ 3) W.model ∞ (X.outerModelHomeomorph hport hlin).symm
      (outerFillingSignedModel q (t, 0)) := by
  apply smoothAt_of_partial_comp (outerFillingSignedModel q)
    (X.outerModelHomeomorph hport hlin).symm
    (by rw [outerFillingSignedModel_source]; exact ⟨by norm_num, by norm_num⟩)
  have hx : X.outerBasisParam (t, 0) ∈
      (B.presentation.seam (B.seam (normalFillingIndex q))).source := by
    rw [B.presentation.seam_source]
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    exact ⟨by norm_num, by norm_num⟩
  have h := ((B.presentation.seam (B.seam (normalFillingIndex q))).contMDiffOn.contMDiffAt
    ((B.presentation.seam (B.seam (normalFillingIndex q))).open_source.mem_nhds hx)).comp
      (t, 0) X.outerBasisParam.contMDiffAt
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [X.outerGerm_nhds t] with p hp
  have he := congrArg (X.outerModelHomeomorph hport hlin).symm
    (X.outerModelHomeomorph_seam hport hlin p.1 p.2 hp)
  rw [Homeomorph.symm_apply_apply] at he
  exact he.symm

end GC.Seifert

namespace GC.Seifert

def outerFillingOpenCap : TopologicalSpace.Opens (ℂ × Circle) :=
  ⟨{y | ‖y.1‖ < 1}, isOpen_lt continuous_fst.norm continuous_const⟩

def outerFillingCapOfPoint (y : outerFillingOpenCap) : solidSet.{u} :=
  ⟨(ULift.up ((3 : ℂ) * y.val.1), y.val.2), by
    apply (mem_discSet_iff (ULift.up ((3 : ℂ) * y.val.1) : PlaneLift.{u})).mpr
    rw [norm_mul, Complex.norm_ofNat]
    have hy : ‖y.val.1‖ < 1 := y.property
    nlinarith⟩

theorem outerFillingCapOfPoint_smooth :
    ContMDiff PlaneCircleModel (𝓡∂ 3) ∞ outerFillingCapOfPoint.{u} := by
  apply (solidAtlas.contMDiff_iff_subtype_val _).mpr
  exact (contMDiff_planeLift_up.comp
    (((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_fst).comp
      contMDiff_subtype_val)).prodMk (contMDiff_snd.comp contMDiff_subtype_val)

theorem outerFillingCapNormalize_ofPoint (y : outerFillingOpenCap) :
    outerFillingCapNormalize (outerFillingCapOfPoint.{u} y) = y.val := by
  apply Prod.ext
  · change ((3 : ℂ) * y.val.1) / 3 = y.val.1
    ring
  · rfl

variable {W : CompactCarrier.{u}} {q : ℤ} {B : SeifertBlock W (selectedNormalData q)}
variable (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))

theorem NormalFillingTrivializations.outerModelHomeomorph_inverse_host (y :
    ElementaryPresentation.outerHostTarget.{u}) :
    (X.outerModelHomeomorph hport hlin).symm y.val =
      B.presentation.cutMap (X.cutDiffeomorph (Sum.inl (productDiffeomorph 3
        ((ElementaryPresentation.outerHostDiffeomorph q).symm y).val))) := by
  apply (X.outerModelHomeomorph hport hlin).injective
  rw [Homeomorph.apply_symm_apply, X.outerModelHomeomorph_cutMap]
  change y.val = outerFillingCutModel q (X.cutDiffeomorph.symm (X.cutDiffeomorph _))
  rw [Diffeomorph.symm_apply_apply]
  change y.val = ElementaryPresentation.outerCappingHostProduct q
    ((productDiffeomorph 3).symm (productDiffeomorph 3 _))
  rw [Diffeomorph.symm_apply_apply]
  exact (congrArg Subtype.val
    ((ElementaryPresentation.outerHostDiffeomorph q).apply_symm_apply y)).symm

theorem NormalFillingTrivializations.outerModelHomeomorph_inverse_host_smooth
    (y : ElementaryPresentation.outerCappingProductSet.{u})
    (hy : y ∈ ElementaryPresentation.outerHostTarget.{u}) :
    ContMDiffAt (𝓡∂ 3) W.model ∞ (X.outerModelHomeomorph hport hlin).symm y := by
  have hg : ContMDiff (𝓡∂ 3) W.model ∞
      (fun z : ElementaryPresentation.outerHostTarget.{u} =>
        (X.outerModelHomeomorph hport hlin).symm z.val) := by
    have he := funext (X.outerModelHomeomorph_inverse_host hport hlin)
    rw [he]
    exact B.presentation.quotient_smooth.comp (X.cutDiffeomorph.contMDiff.comp
      (ContMDiff.inl.comp ((productDiffeomorph 3).contMDiff.comp
        (contMDiff_subtype_val.comp
          (ElementaryPresentation.outerHostDiffeomorph q).symm.contMDiff))))
  exact contMDiffAt_subtype_iff.mp (hg.contMDiffAt (x := ⟨y, hy⟩))

theorem NormalFillingTrivializations.outerModelHomeomorph_inverse_cap
    (y : outerFillingOpenCap) :
    (X.outerModelHomeomorph hport hlin).symm (normalOuterTubeAtlas q 0 y.val) =
      B.presentation.cutMap (X.cutDiffeomorph (Sum.inr (outerFillingCapOfPoint.{u} y))) := by
  apply (X.outerModelHomeomorph hport hlin).injective
  rw [Homeomorph.apply_symm_apply, X.outerModelHomeomorph_cutMap]
  change normalOuterTubeAtlas q 0 y.val =
    outerFillingCutModel q (X.cutDiffeomorph.symm (X.cutDiffeomorph _))
  rw [Diffeomorph.symm_apply_apply]
  change normalOuterTubeAtlas q 0 y.val = normalOuterTubeAtlas q 0
    (outerFillingCapNormalize (outerFillingCapOfPoint.{u} y))
  rw [outerFillingCapNormalize_ofPoint]

theorem NormalFillingTrivializations.outerModelHomeomorph_inverse_cap_smooth
    (y : ℂ × Circle) (hy : ‖y.1‖ < 1) :
    ContMDiffAt (𝓡∂ 3) W.model ∞ (X.outerModelHomeomorph hport hlin).symm
      (normalOuterTubeAtlas q 0 y) := by
  apply smoothAt_of_partial_comp (normalOuterTubeAtlas q 0)
    (X.outerModelHomeomorph hport hlin).symm
    (by rw [normalOuterTubeAtlas_source]; exact lt_trans hy (by norm_num))
  have hg : ContMDiff PlaneCircleModel W.model ∞
      (fun z : outerFillingOpenCap =>
        (X.outerModelHomeomorph hport hlin).symm (normalOuterTubeAtlas q 0 z.val)) := by
    have he := funext (X.outerModelHomeomorph_inverse_cap hport hlin)
    rw [he]
    exact B.presentation.quotient_smooth.comp (X.cutDiffeomorph.contMDiff.comp
      (ContMDiff.inr.comp outerFillingCapOfPoint_smooth))
  exact (contMDiffAt_subtype_iff (f := (X.outerModelHomeomorph hport hlin).symm ∘
    normalOuterTubeAtlas q 0)).mp (hg.contMDiffAt (x := ⟨y, hy⟩))

end GC.Seifert

namespace GC.Seifert

theorem outerFillingSignedModel_zero (q : ℤ) (t : Torus) :
    outerFillingSignedModel.{u} q (t, 0) = normalOuterTubeAtlas q 0 ((t.1 : ℂ), t.2) := by
  change normalOuterTubeAtlas q 0 ((seamRadius 1 0 / 3) • (t.1 : ℂ), t.2) = _
  norm_num [seamRadius]

theorem outerFillingSignedModel_host_zero (q : ℤ) (t : Torus) :
    outerFillingSignedModel.{u} q (t, 0) =
      ElementaryPresentation.outerCappingHostProduct q
        (planarCollar 3 (Or.inr rfl) 0 (((Merge.sectionFilling q).matching t).1, halfZero),
          ((Merge.sectionFilling q).matching t).2) := by
  rw [outerFillingSignedModel_cap q t 0 (by norm_num) le_rfl]
  have hz : halfPoint (-(0 : ℝ)) (neg_nonneg.mpr (le_refl 0)) = halfZero := by
    exact halfPoint_eq_self halfZero _ (by change -(0 : ℝ) = 0; norm_num)
  rw [hz]
  change outerFillingCutModel q (Sum.inr (solidCollar 1 (t, halfZero))) = _
  rw [outerFillingCutModel_boundary]
  change ElementaryPresentation.outerCappingHostProduct q
    ((productDiffeomorph 3).symm (productDiffeomorph 3 _)) = _
  rw [Diffeomorph.symm_apply_apply]

variable {W : CompactCarrier.{u}} {q : ℤ} {B : SeifertBlock W (selectedNormalData q)}
variable (X : NormalFillingTrivializations B)
    (hport : B.port (.inr (normalFillingIndex q)) = 0)
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q)))))

theorem NormalFillingTrivializations.outerModelHomeomorph_inverse_smooth :
    ContMDiff (𝓡∂ 3) W.model ∞ (X.outerModelHomeomorph hport hlin).symm := by
  intro y
  obtain ⟨a, rfl⟩ := outerFillingCutModel_surjective q y
  rcases a with a | a
  · let x := (productDiffeomorph 3).symm a
    change ContMDiffAt (𝓡∂ 3) W.model ∞ (X.outerModelHomeomorph hport hlin).symm
      (ElementaryPresentation.outerCappingHostProduct q x)
    have hxle : ‖x.1.val.down‖ ≤ 3 :=
      ((mem_planarSet_iff (Or.inr rfl) _).mp x.1.property).1
    by_cases hx : ‖x.1.val.down‖ < 3
    · exact X.outerModelHomeomorph_inverse_host_smooth hport hlin _
        (ElementaryPresentation.outerCappingHostProduct_mem_hostTarget q x hx)
    · have hn : ‖x.1.val.down‖ = 3 := le_antisymm hxle (not_lt.mp hx)
      let τ := unitOf x.1.val.down
      let t := (Merge.sectionFilling q).matching.symm (τ, x.2)
      have ht : (Merge.sectionFilling q).matching t = (τ, x.2) :=
        (Merge.sectionFilling q).matching.apply_symm_apply _
      have hb : x.1 = planarCollar 3 (Or.inr rfl) 0 (τ, halfZero) := by
        apply Subtype.ext
        apply ULift.ext
        rw [planarCollar_zero_val]
        have hcircle : planarCircleMap 3 0 τ = (3 : ℝ) • (τ : ℂ) := by
          simp [planarCircleMap, planarCenter, planarRadius]
        rw [hcircle]
        have h := norm_smul_unitOf x.1.val.down
        rw [hn] at h
        exact h.symm
      have he : x = (planarCollar 3 (Or.inr rfl) 0
          (((Merge.sectionFilling q).matching t).1, halfZero),
            ((Merge.sectionFilling q).matching t).2) := by
        rw [ht]
        exact Prod.ext hb rfl
      rw [he, ← outerFillingSignedModel_host_zero]
      exact X.outerModelHomeomorph_inverse_seam_smooth hport hlin t
  · change ContMDiffAt (𝓡∂ 3) W.model ∞ (X.outerModelHomeomorph hport hlin).symm
      (normalOuterTubeAtlas q 0 (outerFillingCapNormalize a))
    have hn := outerFillingCapNormalize_norm a
    by_cases hlt : ‖(outerFillingCapNormalize a).1‖ < 1
    · exact X.outerModelHomeomorph_inverse_cap_smooth hport hlin _ hlt
    · have heq : ‖(outerFillingCapNormalize a).1‖ = 1 :=
        le_antisymm hn (not_lt.mp hlt)
      let t := (unitOf (outerFillingCapNormalize a).1, (outerFillingCapNormalize a).2)
      have he : outerFillingCapNormalize a = ((t.1 : ℂ), t.2) := by
        apply Prod.ext
        · have h := norm_smul_unitOf (outerFillingCapNormalize a).1
          rw [heq, one_smul] at h
          exact h.symm
        · rfl
      rw [he, ← outerFillingSignedModel_zero]
      exact X.outerModelHomeomorph_inverse_seam_smooth hport hlin t

def NormalFillingTrivializations.outerModelDiffeomorph :
    W.Carrier ≃ₘ⟮W.model, 𝓡∂ 3⟯ ElementaryPresentation.outerCappingProductSet.{u} where
  toEquiv := (X.outerModelHomeomorph hport hlin).toEquiv
  contMDiff_toFun := X.outerModelHomeomorph_smooth hport hlin
  contMDiff_invFun := X.outerModelHomeomorph_inverse_smooth hport hlin

end GC.Seifert

namespace GC.Seifert

theorem SeifertBlock.exists_normalAnnulusProduct {W : CompactCarrier.{u}} {q : ℤ}
    (B : SeifertBlock W (selectedNormalData q))
    (hlin : B.presentation.pairing.matching (B.seam (normalFillingIndex q)) =
      linearTorusDiffeomorph (torusUnit
        (B.presentation.pairing.matching (B.seam (normalFillingIndex q))))) :
    Nonempty ((planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), W.model⟯ W.Carrier) := by
  obtain ⟨X⟩ := B.exists_normalFillingTrivializations
  rcases ConeFilling.fin_three_cases (B.port (.inr (normalFillingIndex q))) with hp | hp | hp
  · exact ⟨ElementaryPresentation.outerCappingAnnulusProductDiffeomorph.trans
      (X.outerModelDiffeomorph hp hlin).symm⟩
  · exact ⟨(ElementaryPresentation.sectionCappingAnnulusProductDiffeomorph q).trans
      (X.innerModelDiffeomorph hp hlin)⟩
  · exact ⟨(ElementaryPresentation.sectionCappingAnnulusProductDiffeomorph q).trans
      (X.innerTwoModelDiffeomorph hp hlin)⟩

namespace ElementaryPresentation
variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem exists_fillingProductDiffeomorph_of_linear (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
    (hk3 : E.kind (E.hostPiece j b) = 3) (hlin : E.IsLinearSeam j) :
    Nonempty ((planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier) := by
  obtain ⟨q, hq⟩ := h.exists_mergeSlope_eq
  exact (E.fillingSelectedBlock j b h hk3 q hq).exists_normalAnnulusProduct
    (E.fillingSelectedBlock_matching_linear j b h hk3 q hq hlin (normalFillingIndex q))

theorem exists_fillingProductDiffeomorph (hT : TorusMappingClassLinear)
    (E : ElementaryPresentation (NoCuts.carrier Q)) (j : Fin E.toTorus.pairing.count)
    (b : Bool) (h : E.IsMergeSeam j b) (hk3 : E.kind (E.hostPiece j b) = 3) :
    Nonempty ((planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1),
      (fillingProductCarrier E j).model⟯ (fillingProductCarrier E j).Carrier) := by
  have h' : (E.linearize hT).IsMergeSeam j b := (E.isMergeSeam_linearize hT j b).mpr h
  have hk3' : (E.linearize hT).kind ((E.linearize hT).hostPiece j b) = 3 := by
    change E.kind ((E.linearize hT).seamPiece j (!b)) = 3
    rw [E.seamPiece_linearize]
    exact hk3
  exact (E.linearize hT).exists_fillingProductDiffeomorph_of_linear j b h' hk3'
    (E.hasLinearSeams_linearize hT j)

end ElementaryPresentation
end GC.Seifert
