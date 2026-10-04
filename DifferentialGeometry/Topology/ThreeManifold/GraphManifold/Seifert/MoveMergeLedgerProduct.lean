import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerLocal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingProductCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassProof

/-!
# The actual pants merge product of a mixed selected quotient

The two non-frozen selected pieces form a genuine one-filling Seifert block on their actual
quotient. Its normal filling has distance one and gives an annulus product on the whole carrier.
The proved torus mapping-class theorem linearizes this local block without changing its carrier.
No product model is assigned to unrelated frozen pieces and omitted self seams remain boundary.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert
namespace ElementaryPresentation
variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b)
  (hk3 : E.kind (E.hostPiece j b) = 3) (q : ℤ) (hq : E.mergeSlope j b = Merge.sectionSlope q)

def normalWholeGroup :
    SelectedStarGroup (E.toTorus.flipSeams (fun k => by clear k; exact !b))
      (selectedNormalData q) where
  center := E.hostPiece j b
  product := (E.pieceOfKind hk3).flip (fun k => by clear k; exact !b)
  arm l := by clear l; exact j
  solid l := by
    clear l
    have hl : (E.toTorus.flipSeams (fun k => by clear k; exact !b)).leftPiece j =
        E.seamPiece j b := by cases b <;> rfl
    exact ((E.pieceOfKind h.kind_seamPiece).flip (fun k => by clear k; exact !b)).congrIndex
      hl.symm
  arm_right l := by clear l; cases b <;> rfl
  arm_injective l l' _he := by
    change Fin 1 at l l'
    exact Subsingleton.elim l l'
  solid_ne_center l := by
    clear l
    have hl : (E.toTorus.flipSeams (fun k => by clear k; exact !b)).leftPiece j =
        E.seamPiece j b := by cases b <;> rfl
    rw [hl]
    exact h.seamPiece_ne_hostPiece
  slope l := by
    change Fin 1 at l
    obtain rfl : l = 0 := Subsingleton.elim l 0
    have hm : (E.toTorus.flipSeams (fun k => by clear k; exact !b)).pairing.matching j =
        E.crossMap j b := by cases b <;> rfl
    rw [hm]
    change torusUnit (E.crossMap j b) • meridianSlope = Merge.sectionSlope q
    cases b
    · simpa only [ElementaryPresentation.crossMap, ElementaryPresentation.mergeSlope,
        torusUnit_symm] using hq
    · exact hq

theorem normalWholeGroup_cover (hc : E.toTorus.components.count = 2) :
    ∀ i, i ∈ (E.normalWholeGroup j b h hk3 q hq).set := by
  let G := E.normalWholeGroup j b h hk3 q hq
  let m := normalFillingIndex q
  have hs : ({G.center, ((E.toTorus.flipSeams (fun k => by clear k; exact !b)).leftPiece
      (G.arm m))} : Finset (Fin E.toTorus.components.count)) ⊆ G.set := by
    intro i hi
    rcases Finset.mem_insert.mp hi with he | hi
    · exact he ▸ G.center_mem
    · exact (Finset.mem_singleton.mp hi) ▸ G.solid_mem m
  have hcG : 2 ≤ G.set.card := by
    have hh := Finset.card_le_card hs
    have hcard : ({G.center, ((E.toTorus.flipSeams (fun k => by clear k; exact !b)).leftPiece
        (G.arm m))} : Finset (Fin E.toTorus.components.count)).card = 2 :=
      Finset.card_pair (G.solid_ne_center m).symm
    exact hcard ▸ hh
  have he : G.set = Finset.univ := Finset.eq_of_subset_of_card_le
    (Finset.subset_univ G.set) (by
      rw [Finset.card_univ, Fintype.card_fin]
      change E.toTorus.components.count ≤ G.set.card
      exact le_of_eq_of_le hc hcG)
  intro i
  rw [he]
  exact Finset.mem_univ i

theorem normalWholeGroup_seams (hp : E.toTorus.pairing.count = 1) :
    ∀ k, k ∈ (E.normalWholeGroup j b h hk3 q hq).selected := by
  let G := E.normalWholeGroup j b h hk3 q hq
  have : Subsingleton (Fin (E.toTorus.flipSeams (fun k => by clear k; exact !b)).pairing.count) :=
    Fintype.card_le_one_iff_subsingleton.mp (by
      rw [Fintype.card_fin]
      change E.toTorus.pairing.count ≤ 1
      omega)
  intro k
  exact (Subsingleton.elim k (G.arm (normalFillingIndex q))).symm ▸
    G.arm_mem (normalFillingIndex q)

include j b h hk3 q hq in
theorem exists_normalWholeProduct (hc : E.toTorus.components.count = 2)
    (hp : E.toTorus.pairing.count = 1) :
    Nonempty ((planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), W.model⟯ W.Carrier) := by
  let B := (E.normalWholeGroup j b h hk3 q hq).wholeBlock
    (E.normalWholeGroup_cover j b h hk3 q hq hc) (E.normalWholeGroup_seams j b h hk3 q hq hp)
  exact (B.linearized torusMappingClassLinear_holds).exists_normalAnnulusProduct
    (B.linearized_matching torusMappingClassLinear_holds (normalFillingIndex q))

end ElementaryPresentation
namespace RelativeNormalization.MixedStage
variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

theorem exists_selectedPantsMergeProduct (j : Fin σ.toTorus.pairing.count) (b : Bool)
    (h : σ.IsMergeSeam j b) (hk3 : σ.kind (σ.hostPiece j b) = 3) :
    ∃ B : PlanarBase.{u} 2, Nonempty
      ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
        (σ.selectedCarrier j).model⟯ (σ.selectedCarrier j).Carrier) := by
  let E := σ.selectedElementary j h.1
  have hm := σ.selectedElementary_isMergeSeam j b h
  have hkind : E.kind (E.hostPiece (σ.selectedIndex j) b) = 3 :=
    (σ.selectedElementary_hostPiece_kind j h.1 b).trans hk3
  have hn : σ.toTorus.leftPiece j ≠ σ.toTorus.rightPiece j := by
    intro he
    have hh : σ.seamPiece j b = σ.hostPiece j b := by
      cases b
      · exact he.symm
      · exact he
    have hge := h.2.2.1
    rw [← hh, h.2.1] at hge
    omega
  have hc : E.toTorus.components.count = 2 := by
    change (σ.toTorus.seamPair j).card = 2
    exact Finset.card_pair hn
  obtain ⟨q, hq⟩ := hm.exists_mergeSlope_eq
  exact ⟨annulusPlanarBase, E.exists_normalWholeProduct (σ.selectedIndex j) b hm hkind q hq
    hc (σ.selectedElementary_pairing_count j h.1)⟩

end RelativeNormalization.MixedStage
end GC.Seifert
