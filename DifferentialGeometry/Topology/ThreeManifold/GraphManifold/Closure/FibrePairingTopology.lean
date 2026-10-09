import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawFibreComplement

/-!
The actual excised cut carrier retains the original finite gluing and whole quotient square.
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
variable (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : _root_.Topology.IsEmbedding ι)
variable (hrange : range ι = G.FibreCutComplement φ)

include h3 hI hrange in
private theorem fibreRetainedBlock_range (j : Fin G.pairing.count) :
    G.pairing.gluing.block j ⊆ range ι := by
  intro x hx
  rw [hrange]
  rintro ⟨p, hp, rfl⟩
  have hs : p ∈ φ.source := h3 (by
    change ‖p.1.down‖ < 1 at hp
    change ‖p.1.down‖ ≤ 3
    linarith)
  have hi := hI (φ.map_source hs)
  have hb : G.cutCarrier.model.IsBoundaryPoint (φ p) := by
    change φ p ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
    rw [G.cut_boundary_exhausted]
    exact Or.inl (mem_iUnion.mpr ⟨j, hx⟩)
  exact (G.cutCarrier.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hi hb

private def fibreRetainedLeftHomeomorph (j : Fin G.pairing.count) :
    (ι ⁻¹' G.pairing.gluing.left j) ≃ₜ G.pairing.gluing.left j :=
  hι.homeomorphOfSubsetRange (fun x hx =>
    G.fibreRetainedBlock_range φ h3 hI K ι hrange j
      (show x ∈ G.pairing.gluing.block j from Or.inl hx))

private def fibreRetainedRightHomeomorph (j : Fin G.pairing.count) :
    (ι ⁻¹' G.pairing.gluing.right j) ≃ₜ G.pairing.gluing.right j :=
  hι.homeomorphOfSubsetRange (fun x hx =>
    G.fibreRetainedBlock_range φ h3 hI K ι hrange j
      (show x ∈ G.pairing.gluing.block j from Or.inr hx))

private theorem fibreRetainedLeftHomeomorph_apply (j : Fin G.pairing.count)
    (x : ι ⁻¹' G.pairing.gluing.left j) :
    (G.fibreRetainedLeftHomeomorph φ h3 hI K ι hι hrange j x).val = ι x.val := by
  exact hι.homeomorphOfSubsetRange_apply_coe _ x

private theorem fibreRetainedRightHomeomorph_apply (j : Fin G.pairing.count)
    (x : ι ⁻¹' G.pairing.gluing.right j) :
    (G.fibreRetainedRightHomeomorph φ h3 hI K ι hι hrange j x).val = ι x.val := by
  exact hι.homeomorphOfSubsetRange_apply_coe _ x

private theorem fibreRetainedLeftHomeomorph_symm_apply (j : Fin G.pairing.count)
    (x : G.pairing.gluing.left j) :
    ι ((G.fibreRetainedLeftHomeomorph φ h3 hI K ι hι hrange j).symm x).val = x.val := by
  have h := congrArg Subtype.val
    ((G.fibreRetainedLeftHomeomorph φ h3 hI K ι hι hrange j).apply_symm_apply x)
  rw [G.fibreRetainedLeftHomeomorph_apply] at h
  exact h

private theorem fibreRetainedRightHomeomorph_symm_apply (j : Fin G.pairing.count)
    (x : G.pairing.gluing.right j) :
    ι ((G.fibreRetainedRightHomeomorph φ h3 hI K ι hι hrange j).symm x).val = x.val := by
  have h := congrArg Subtype.val
    ((G.fibreRetainedRightHomeomorph φ h3 hI K ι hι hrange j).apply_symm_apply x)
  rw [G.fibreRetainedRightHomeomorph_apply] at h
  exact h

def fibreRetainedGluing : BoundaryGluing K.Carrier (Fin G.pairing.count) where
  left j := ι ⁻¹' G.pairing.gluing.left j
  right j := ι ⁻¹' G.pairing.gluing.right j
  attaching j := ((G.fibreRetainedLeftHomeomorph φ h3 hI K ι hι hrange j).trans
    (G.pairing.gluing.attaching j)).trans
      (G.fibreRetainedRightHomeomorph φ h3 hI K ι hι hrange j).symm
  isClosed_left j := (G.pairing.gluing.isClosed_left j).preimage hι.continuous
  isClosed_right j := (G.pairing.gluing.isClosed_right j).preimage hι.continuous
  disjoint_left_right j := (G.pairing.gluing.disjoint_left_right j).preimage ι
  disjoint_blocks i j hij := by
    simpa only [preimage_union] using (G.pairing.gluing.disjoint_blocks i j hij).preimage ι

def fibreRetainedLeftParam (j : Fin G.pairing.count) :
    Torus ≃ₜ (G.fibreRetainedGluing φ h3 hI K ι hι hrange).left j :=
  (G.pairing.leftParam j).trans
    (G.fibreRetainedLeftHomeomorph φ h3 hI K ι hι hrange j).symm

def fibreRetainedRightParam (j : Fin G.pairing.count) :
    Torus ≃ₜ (G.fibreRetainedGluing φ h3 hI K ι hι hrange).right j :=
  (G.pairing.rightParam j).trans
    (G.fibreRetainedRightHomeomorph φ h3 hI K ι hι hrange j).symm

theorem fibreRetainedLeftParam_apply (j : Fin G.pairing.count) (t : Torus) :
    ι (G.fibreRetainedLeftParam φ h3 hI K ι hι hrange j t).val =
      (G.pairing.leftParam j t).val := by
  exact G.fibreRetainedLeftHomeomorph_symm_apply φ h3 hI K ι hι hrange j
    (G.pairing.leftParam j t)

theorem fibreRetainedRightParam_apply (j : Fin G.pairing.count) (t : Torus) :
    ι (G.fibreRetainedRightParam φ h3 hI K ι hι hrange j t).val =
      (G.pairing.rightParam j t).val := by
  exact G.fibreRetainedRightHomeomorph_symm_apply φ h3 hI K ι hι hrange j
    (G.pairing.rightParam j t)

theorem fibreRetainedGluing_matching (j : Fin G.pairing.count) (t : Torus) :
    (G.fibreRetainedGluing φ h3 hI K ι hι hrange).attaching j
      (G.fibreRetainedLeftParam φ h3 hI K ι hι hrange j t) =
      G.fibreRetainedRightParam φ h3 hI K ι hι hrange j (G.pairing.matching j t) := by
  change (G.fibreRetainedRightHomeomorph φ h3 hI K ι hι hrange j).symm
    (G.pairing.gluing.attaching j
      ((G.fibreRetainedLeftHomeomorph φ h3 hI K ι hι hrange j)
        ((G.fibreRetainedLeftHomeomorph φ h3 hI K ι hι hrange j).symm
          (G.pairing.leftParam j t)))) = _
  rw [Homeomorph.apply_symm_apply, G.pairing.matching_eq]
  rfl

def fibreExcisionCutHomeomorph : K.Carrier ≃ₜ G.FibreCutComplement φ := by
  let f : K.Carrier → G.FibreCutComplement φ := fun x =>
    ⟨ι x, hrange ▸ mem_range_self x⟩
  have hf : Bijective f := by
    constructor
    · intro x y h
      exact hι.injective (congrArg Subtype.val h)
    · intro y
      have hy : y.val ∈ range ι := by rw [hrange]; exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
    (hι.continuous.subtype_mk _)

theorem fibreExcisionCutHomeomorph_apply (x : K.Carrier) :
    (G.fibreExcisionCutHomeomorph φ K ι hι hrange x).val = ι x := rfl

theorem fibreRetainedGluing_flip (j : Fin G.pairing.count) (x : K.Carrier) :
    ι ((G.fibreRetainedGluing φ h3 hI K ι hι hrange).flip j x) =
      G.pairing.gluing.flip j (ι x) := by
  classical
  by_cases hl : ι x ∈ G.pairing.gluing.left j
  · rw [(G.fibreRetainedGluing φ h3 hI K ι hι hrange).flip_of_mem_left hl,
      G.pairing.gluing.flip_of_mem_left hl]
    change ι ((G.fibreRetainedRightHomeomorph φ h3 hI K ι hι hrange j).symm
      (G.pairing.gluing.attaching j
        (G.fibreRetainedLeftHomeomorph φ h3 hI K ι hι hrange j ⟨x, hl⟩))).val = _
    rw [G.fibreRetainedRightHomeomorph_symm_apply φ h3 hI K ι hι hrange j]
    congr 1
  · by_cases hr : ι x ∈ G.pairing.gluing.right j
    · rw [(G.fibreRetainedGluing φ h3 hI K ι hι hrange).flip_of_mem_right hr,
        G.pairing.gluing.flip_of_mem_right hr]
      change ι ((G.fibreRetainedLeftHomeomorph φ h3 hI K ι hι hrange j).symm
        ((G.pairing.gluing.attaching j).symm
          (G.fibreRetainedRightHomeomorph φ h3 hI K ι hι hrange j ⟨x, hr⟩))).val = _
      rw [G.fibreRetainedLeftHomeomorph_symm_apply φ h3 hI K ι hι hrange j]
      congr 1
    · rw [(G.fibreRetainedGluing φ h3 hI K ι hι hrange).flip_of_notMem
        (not_or.mpr ⟨hl, hr⟩), G.pairing.gluing.flip_of_notMem (not_or.mpr ⟨hl, hr⟩)]

theorem fibreRetainedGluing_rel_iff (x y : K.Carrier) :
    (G.fibreRetainedGluing φ h3 hI K ι hι hrange).rel x y ↔
      G.pairing.gluing.rel (ι x) (ι y) := by
  constructor
  · rintro (rfl | ⟨j, hx, he⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨j, hx, (congrArg ι he).trans
        (G.fibreRetainedGluing_flip φ h3 hI K ι hι hrange j x)⟩
  · rintro (he | ⟨j, hx, he⟩)
    · exact Or.inl (hι.injective he)
    · exact Or.inr ⟨j, hx, hι.injective
        (he.trans (G.fibreRetainedGluing_flip φ h3 hI K ι hι hrange j x).symm)⟩

def fibreRetainedQuotientHomeomorph :
    Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hrange).setoid ≃ₜ
      G.FibreAmbientComplement φ h3 hI :=
  ((G.fibreRetainedGluing φ h3 hI K ι hι hrange).congrHomeomorph
    (G.fibreComplementGluing φ h3 hI) (G.fibreExcisionCutHomeomorph φ K ι hι hrange)
      (fun x y => (G.fibreRetainedGluing_rel_iff φ h3 hI K ι hι hrange x y).trans
        (G.fibreComplementGluing_rel_iff φ h3 hI
          (G.fibreExcisionCutHomeomorph φ K ι hι hrange x)
          (G.fibreExcisionCutHomeomorph φ K ι hι hrange y)).symm)).trans
    (G.fibreComplementGluingQuotientHomeomorph φ h3 hI)

theorem fibreRetainedQuotientHomeomorph_apply (x : K.Carrier) :
    (G.fibreRetainedQuotientHomeomorph φ h3 hI K ι hι hrange (Quotient.mk'' x)).val =
      G.reconstruction (G.pairing.quotientMap (ι x)) := rfl

end GC.GraphManifold.RawGraphPresentation
