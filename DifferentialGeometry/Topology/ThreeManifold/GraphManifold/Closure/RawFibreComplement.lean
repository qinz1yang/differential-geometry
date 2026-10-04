import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawFibreTube

/-!
The original raw pairing relation reconstructs the same ambient regular-fibre complement.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawGraphPresentation

variable {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
  (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
variable (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
variable (hI : φ.target ⊆ G.cutCarrier.interior)

abbrev FibreCutComplement := {x : G.cutCarrier.Carrier |
  x ∉ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1}}

abbrev FibreAmbientComplement := {x : W.Carrier |
  x ∉ (G.transportRegularFibreTube φ h3 hI) ''
    {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1}}

include h3 in
private theorem fibreOpenDisc_source :
    {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1} ⊆ φ.source := by
  intro p hp
  exact h3 (by change ‖p.1.down‖ ≤ 3; change ‖p.1.down‖ < 1 at hp; linarith)

include h3 hI in
private theorem fibreRemoved_not_block {x : G.cutCarrier.Carrier}
    (hx : x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})
    (j : Fin G.pairing.count) : x ∉ G.pairing.gluing.block j := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hi := hI (φ.toPartialEquiv.map_source (G.fibreOpenDisc_source φ h3 hp))
  intro hb
  have hboundary : G.cutCarrier.model.IsBoundaryPoint (φ p) := by
    change φ p ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
    rw [G.cut_boundary_exhausted]
    exact Or.inl (mem_iUnion.mpr ⟨j, hb⟩)
  exact (G.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi hboundary

include h3 hI in
theorem fibreRemoved_saturated {x y : G.cutCarrier.Carrier}
    (h : G.pairing.gluing.rel x y) :
    (x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1}) ↔
      y ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1} := by
  constructor
  · intro hx
    exact (G.pairing.gluing.eq_of_rel_of_notMem
      (G.fibreRemoved_not_block φ h3 hI hx) h) ▸ hx
  · intro hy
    exact (G.pairing.gluing.eq_of_rel_of_notMem
      (G.fibreRemoved_not_block φ h3 hI hy) (G.pairing.gluing.isEquivalence_rel.symm h)) ▸ hy

include h3 in
theorem fibreCutComplementCompact : CompactSpace (G.FibreCutComplement φ) := by
  have ho : IsOpen (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1}) :=
    φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_lt ((continuous_uliftDown.comp continuous_fst).norm) continuous_const)
      (G.fibreOpenDisc_source φ h3)
  exact isCompact_iff_compactSpace.mp ho.isClosed_compl.isCompact

def fibreComplementSetoid : Setoid (G.FibreCutComplement φ) :=
  Setoid.comap Subtype.val G.pairing.gluing.setoid

private theorem fibreComplement_map_mem (x : G.FibreCutComplement φ) :
    G.reconstruction (G.pairing.quotientMap x.val) ∈
      (G.FibreAmbientComplement φ h3 hI : Set W.Carrier) := by
  change G.reconstruction (G.pairing.quotientMap x.val) ∉ _
  rw [G.transportRegularFibreTube_openDisc_image φ h3 hI]
  rintro ⟨y, hy, he⟩
  have heq : G.pairing.quotientMap y = G.pairing.quotientMap x.val :=
    G.reconstruction.injective he
  exact x.property ((G.fibreRemoved_saturated φ h3 hI
    ((Quotient.eq' (s₁ := G.pairing.gluing.setoid)).mp heq)).mp hy)

def fibreComplementMap : C(G.FibreCutComplement φ, G.FibreAmbientComplement φ h3 hI) :=
  ⟨fun x => ⟨G.reconstruction (G.pairing.quotientMap x.val),
      G.fibreComplement_map_mem φ h3 hI x⟩,
    (G.reconstruction.continuous.comp
      (G.pairing.quotientMap.continuous.comp continuous_subtype_val)).subtype_mk _⟩

private theorem fibreComplementMap_eq_iff (x y : G.FibreCutComplement φ) :
    G.fibreComplementMap φ h3 hI x = G.fibreComplementMap φ h3 hI y ↔
      G.fibreComplementSetoid φ x y := by
  rw [Subtype.ext_iff]
  change G.reconstruction (G.pairing.quotientMap x.val) =
    G.reconstruction (G.pairing.quotientMap y.val) ↔ G.pairing.gluing.setoid x.val y.val
  rw [G.reconstruction.injective.eq_iff]
  exact Quotient.eq'

private theorem fibreComplementMap_surjective : Surjective (G.fibreComplementMap φ h3 hI) := by
  intro y
  obtain ⟨x, hx⟩ := Quotient.exists_rep (G.reconstruction.symm y.val)
  have he : G.reconstruction (G.pairing.quotientMap x) = y.val := by
    exact (congrArg G.reconstruction hx).trans (G.reconstruction.apply_symm_apply y.val)
  have hm : x ∈ (G.FibreCutComplement φ : Set G.cutCarrier.Carrier) := by
    intro hxD
    apply y.property
    rw [G.transportRegularFibreTube_openDisc_image φ h3 hI]
    exact ⟨x, hxD, he⟩
  exact ⟨⟨x, hm⟩, Subtype.ext he⟩

private def fibreComplementLift :
    Quotient (G.fibreComplementSetoid φ) → G.FibreAmbientComplement φ h3 hI :=
  Quotient.lift (G.fibreComplementMap φ h3 hI)
    (fun x y h => (G.fibreComplementMap_eq_iff φ h3 hI x y).mpr h)

private theorem fibreComplementLift_continuous : Continuous (G.fibreComplementLift φ h3 hI) :=
  continuous_quot_lift _ (G.fibreComplementMap φ h3 hI).continuous

private theorem fibreComplementLift_bijective : Bijective (G.fibreComplementLift φ h3 hI) := by
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    exact Quotient.sound ((G.fibreComplementMap_eq_iff φ h3 hI a b).mp h)
  · intro y
    obtain ⟨x, hx⟩ := G.fibreComplementMap_surjective φ h3 hI y
    exact ⟨Quotient.mk'' x, hx⟩

def fibreComplementQuotientHomeomorph :
    Quotient (G.fibreComplementSetoid φ) ≃ₜ G.FibreAmbientComplement φ h3 hI := by
  let := G.fibreCutComplementCompact φ h3
  let e := Equiv.ofBijective (G.fibreComplementLift φ h3 hI)
    (G.fibreComplementLift_bijective φ h3 hI)
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (G.fibreComplementLift_continuous φ h3 hI)

theorem fibreComplementQuotientHomeomorph_apply (x : G.FibreCutComplement φ) :
    (G.fibreComplementQuotientHomeomorph φ h3 hI (Quotient.mk'' x)).val =
      G.reconstruction (G.pairing.quotientMap x.val) := rfl

private def fibreComplementBoundaryHomeomorph (A : Set G.cutCarrier.Carrier)
    (hA : A ⊆ G.FibreCutComplement φ) :
    A ≃ₜ (Subtype.val ⁻¹' A : Set (G.FibreCutComplement φ)) where
  toFun x := ⟨⟨x.val, hA x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv x := Subtype.ext (Eq.refl x.val)
  right_inv x := Subtype.ext (Subtype.ext (Eq.refl x.val.val))
  continuous_toFun := (continuous_subtype_val.subtype_mk
    (fun x => hA x.property)).subtype_mk (fun x => x.property)
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x => x.property)

include h3 hI in
private theorem fibreComplement_contains_left (j : Fin G.pairing.count) :
    G.pairing.gluing.left j ⊆ G.FibreCutComplement φ := by
  intro x hx hD
  exact G.fibreRemoved_not_block φ h3 hI hD j (Or.inl hx)

include h3 hI in
private theorem fibreComplement_contains_right (j : Fin G.pairing.count) :
    G.pairing.gluing.right j ⊆ G.FibreCutComplement φ := by
  intro x hx hD
  exact G.fibreRemoved_not_block φ h3 hI hD j (Or.inr hx)

def fibreComplementGluing :
    BoundaryGluing (G.FibreCutComplement φ) (Fin G.pairing.count) where
  left j := Subtype.val ⁻¹' G.pairing.gluing.left j
  right j := Subtype.val ⁻¹' G.pairing.gluing.right j
  attaching j := ((G.fibreComplementBoundaryHomeomorph φ (G.pairing.gluing.left j)
    (G.fibreComplement_contains_left φ h3 hI j)).symm.trans
      (G.pairing.gluing.attaching j)).trans
        (G.fibreComplementBoundaryHomeomorph φ (G.pairing.gluing.right j)
          (G.fibreComplement_contains_right φ h3 hI j))
  isClosed_left j := (G.pairing.gluing.isClosed_left j).preimage continuous_subtype_val
  isClosed_right j := (G.pairing.gluing.isClosed_right j).preimage continuous_subtype_val
  disjoint_left_right j := (G.pairing.gluing.disjoint_left_right j).preimage Subtype.val
  disjoint_blocks i j hij := by
    simpa only [preimage_union] using
      (G.pairing.gluing.disjoint_blocks i j hij).preimage
        (Subtype.val : G.FibreCutComplement φ → G.cutCarrier.Carrier)

theorem fibreComplementGluing_left (j : Fin G.pairing.count) :
    (G.fibreComplementGluing φ h3 hI).left j = Subtype.val ⁻¹' G.pairing.gluing.left j := rfl

theorem fibreComplementGluing_right (j : Fin G.pairing.count) :
    (G.fibreComplementGluing φ h3 hI).right j = Subtype.val ⁻¹' G.pairing.gluing.right j := rfl

theorem fibreComplementGluing_attaching (j : Fin G.pairing.count)
    (x : (G.fibreComplementGluing φ h3 hI).left j) :
    ((G.fibreComplementGluing φ h3 hI).attaching j x).val.val =
      (G.pairing.gluing.attaching j ⟨x.val.val, x.property⟩).val := rfl

theorem fibreComplementGluing_flip (j : Fin G.pairing.count) (x : G.FibreCutComplement φ) :
    ((G.fibreComplementGluing φ h3 hI).flip j x).val = G.pairing.gluing.flip j x.val := by
  classical
  by_cases hl : x.val ∈ G.pairing.gluing.left j
  · have hl' : x ∈ (G.fibreComplementGluing φ h3 hI).left j := hl
    rw [(G.fibreComplementGluing φ h3 hI).flip_of_mem_left hl',
      G.pairing.gluing.flip_of_mem_left hl]
    rfl
  · by_cases hr : x.val ∈ G.pairing.gluing.right j
    · have hr' : x ∈ (G.fibreComplementGluing φ h3 hI).right j := hr
      rw [(G.fibreComplementGluing φ h3 hI).flip_of_mem_right hr',
        G.pairing.gluing.flip_of_mem_right hr]
      rfl
    · have hn : x.val ∉ G.pairing.gluing.block j := not_or.mpr ⟨hl, hr⟩
      have hn' : x ∉ (G.fibreComplementGluing φ h3 hI).block j := hn
      rw [(G.fibreComplementGluing φ h3 hI).flip_of_notMem hn',
        G.pairing.gluing.flip_of_notMem hn]

theorem fibreComplementGluing_rel_iff (x y : G.FibreCutComplement φ) :
    (G.fibreComplementGluing φ h3 hI).rel x y ↔ G.pairing.gluing.rel x.val y.val := by
  constructor
  · rintro (rfl | ⟨j, hx, hxy⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨j, hx, ?_⟩
      exact (congrArg Subtype.val hxy).trans
        (G.fibreComplementGluing_flip φ h3 hI j x)
  · rintro (he | ⟨j, hx, hxy⟩)
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr ⟨j, hx, Subtype.ext
        (hxy.trans (G.fibreComplementGluing_flip φ h3 hI j x).symm)⟩

def fibreComplementGluingQuotientHomeomorph :
    Quotient (G.fibreComplementGluing φ h3 hI).setoid ≃ₜ
      G.FibreAmbientComplement φ h3 hI :=
  (Homeomorph.Quotient.congrRight (G.fibreComplementGluing_rel_iff φ h3 hI)).trans
    (G.fibreComplementQuotientHomeomorph φ h3 hI)

theorem fibreComplementGluingQuotientHomeomorph_apply (x : G.FibreCutComplement φ) :
    (G.fibreComplementGluingQuotientHomeomorph φ h3 hI (Quotient.mk'' x)).val =
      G.reconstruction (G.pairing.quotientMap x.val) := rfl

end GC.GraphManifold.RawGraphPresentation
