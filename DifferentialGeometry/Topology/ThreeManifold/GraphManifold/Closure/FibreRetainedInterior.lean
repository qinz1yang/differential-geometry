import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawFibreAmbient

/-!
The exact interior of the chosen cut complement identifies smoothly with its actual retained
ambient image through genuine partial diffeomorphisms and the original reconstruction square.
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

private def retainedInteriorPoint : G.cutCarrier.interior :=
  ⟨φ (ULift.up 0, 1), hI (φ.toPartialEquiv.map_source (h3 (by simp)))⟩

private def retainedInteriorReconstructionPD :
    PartialDiffeomorph G.cutCarrier.model W.model G.cutCarrier.Carrier W.Carrier ∞ :=
  let x := G.retainedInteriorPoint φ h3 hI
  let a := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    G.cutCarrier.model G.cutCarrier.interior ⟨x⟩
  let b := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    W.model G.interiorImage ⟨G.interiorDiffeomorph x⟩
  (a.symm.trans G.interiorDiffeomorph.toPartialDiffeomorph).trans b

private theorem retainedInteriorReconstructionPD_source :
    (G.retainedInteriorReconstructionPD φ h3 hI).source = G.cutCarrier.interior := by
  let x := G.retainedInteriorPoint φ h3 hI
  let a := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    G.cutCarrier.model G.cutCarrier.interior ⟨x⟩
  let b := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    W.model G.interiorImage ⟨G.interiorDiffeomorph x⟩
  ext y
  change ((y ∈ a.target ∧ a.symm y ∈ univ) ∧
    G.interiorDiffeomorph (a.symm y) ∈ b.source) ↔ y ∈ G.cutCarrier.interior
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target,
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_source]
  simp only [mem_univ, and_true]
  rfl

private theorem retainedInteriorReconstructionPD_apply (y : G.cutCarrier.Carrier)
    (hy : y ∈ G.cutCarrier.interior) :
    G.retainedInteriorReconstructionPD φ h3 hI y = G.reconstruction (G.pairing.quotientMap y) := by
  let x := G.retainedInteriorPoint φ h3 hI
  change (G.interiorDiffeomorph
    ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
      G.cutCarrier.model G.cutCarrier.interior ⟨x⟩).symm y)).val = _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply]
  exact G.interior_map ⟨y, hy⟩

private theorem retainedInteriorReconstruction_closed_iff (x : G.cutCarrier.Carrier)
    (hx : x ∈ G.cutCarrier.interior) :
    G.retainedInteriorReconstructionPD φ h3 hI x ∈
        (G.transportRegularFibreTube φ h3 hI) ''
          {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} ↔
      x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} := by
  rw [G.transportRegularFibreTube_closedDisc_image φ h3 hI]
  constructor
  · rintro ⟨y, ⟨p, hp, he⟩, hy⟩
    have hps : p ∈ φ.source := h3 (by
      change ‖p.1.down‖ ≤ 3
      change ‖p.1.down‖ ≤ 1 at hp
      linarith)
    have hyI : y ∈ G.cutCarrier.interior := he ▸ hI (φ.map_source hps)
    have hyD : y ∈ (G.retainedInteriorReconstructionPD φ h3 hI).source := by
      rw [G.retainedInteriorReconstructionPD_source]
      exact hyI
    have hxD : x ∈ (G.retainedInteriorReconstructionPD φ h3 hI).source := by
      rw [G.retainedInteriorReconstructionPD_source]
      exact hx
    have heq : y = x := (G.retainedInteriorReconstructionPD φ h3 hI).injOn hyD hxD
      ((G.retainedInteriorReconstructionPD_apply φ h3 hI y hyI).trans hy)
    exact ⟨p, hp, he.trans heq⟩
  · intro hxclosed
    exact ⟨x, hxclosed, (G.retainedInteriorReconstructionPD_apply φ h3 hI x hx).symm⟩

variable (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
variable (hι : _root_.Topology.IsEmbedding ι)
variable (hK : range ι = G.FibreCutComplement φ)
variable (hboundary : ι '' K.model.boundary K.Carrier =
  G.cutCarrier.model.boundary G.cutCarrier.Carrier ∪
    range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)))
variable (O_K : PartialDiffeomorph G.cutCarrier.model K.model
  G.cutCarrier.Carrier K.Carrier ∞)
variable (hOKs : O_K.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hOKt : O_K.target = ι ⁻¹' (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hOKi : ∀ x, x ∈ O_K.source → ι (O_K x) = x)
variable (L : CompactCarrier.{u}) (jL : L.Carrier → W.Carrier)
variable (hjL : _root_.Topology.IsEmbedding jL)
variable (O_L : PartialDiffeomorph W.model L.model W.Carrier L.Carrier ∞)
variable (hOLs : O_L.source = ((G.transportRegularFibreTube φ h3 hI) ''
  {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
variable (hOLi : ∀ x, x ∈ O_L.source → jL (O_L x) = x)
variable (ρ : Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hK).setoid ≃ₜ L.Carrier)
variable (hρ : ∀ x : K.Carrier,
  jL (ρ (Quotient.mk'' x)) = G.reconstruction (G.pairing.quotientMap (ι x)))

include hι hK hboundary in
private theorem fibreRetainedInterior_offClosed (x : K.interior) :
    ι x.val ∉ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} := by
  rintro ⟨p, hp, he⟩
  have hxopen : ι x.val ∉ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1} :=
    by
      have he : ι x.val ∈ G.FibreCutComplement φ := hK ▸ mem_range_self x.val
      exact he
  have hpge : 1 ≤ ‖p.1.down‖ := by
    by_contra hlt
    exact hxopen ⟨p, lt_of_not_ge hlt, he⟩
  have hp1 : ‖p.1.down‖ = 1 := le_antisymm hp hpge
  let t : Circle := ⟨p.1.down, mem_sphere_zero_iff_norm.mpr hp1⟩
  have hnew : ι x.val ∈ range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)) := by
    refine ⟨(t, p.2), ?_⟩
    exact he
  have hb : ι x.val ∈ ι '' K.model.boundary K.Carrier := by
    rw [hboundary]
    exact Or.inr hnew
  obtain ⟨y, hy, hey⟩ := hb
  have heq : y = x.val := hι.injective hey
  have hnot := (K.model.isInteriorPoint_iff_not_isBoundaryPoint x.val).mp x.property
  exact hnot (heq ▸ hy)

include hOKi in
private theorem retainedInverse_inclusion (x : K.Carrier) (hx : x ∈ O_K.target) :
    O_K.symm x = ι x := by
  have he := hOKi (O_K.symm x) (O_K.map_target hx)
  have hright : O_K (O_K.symm x) = x := O_K.right_inv hx
  rw [hright] at he
  exact he.symm

def fibreRetainedInteriorPD : PartialDiffeomorph K.model L.model K.Carrier L.Carrier ∞ :=
  (O_K.symm.trans (G.retainedInteriorReconstructionPD φ h3 hI)).trans O_L

include hι hK hboundary hOKs hOKt hOLs in
theorem fibreRetainedInteriorPD_source :
    (G.fibreRetainedInteriorPD φ h3 hI K O_K L O_L).source = K.interior := by
  ext x
  constructor
  · rintro ⟨⟨hx, hy⟩, hz⟩
    change O_K.symm x ∈ (G.retainedInteriorReconstructionPD φ h3 hI).source at hy
    have hyI : O_K.symm x ∈ G.cutCarrier.interior := by
      rwa [G.retainedInteriorReconstructionPD_source] at hy
    have hl := O_K.symm.isLocalDiffeomorphAt K.model G.cutCarrier.model ∞ hx
    exact (hl.isInteriorPoint_iff (by simp)).mpr hyI
  · intro hxI
    have hxoff := G.fibreRetainedInterior_offClosed φ K ι hι hK hboundary ⟨x, hxI⟩
    have hx : x ∈ O_K.target := by
      rw [hOKt]
      exact hxoff
    have hl := O_K.symm.isLocalDiffeomorphAt K.model G.cutCarrier.model ∞ hx
    have hyI : O_K.symm x ∈ G.cutCarrier.interior :=
      (hl.isInteriorPoint_iff (by simp)).mp hxI
    have hyD : O_K.symm x ∈ (G.retainedInteriorReconstructionPD φ h3 hI).source := by
      rw [G.retainedInteriorReconstructionPD_source]
      exact hyI
    refine ⟨⟨hx, hyD⟩, ?_⟩
    change G.retainedInteriorReconstructionPD φ h3 hI (O_K.symm x) ∈ O_L.source
    rw [hOLs]
    apply mt (G.retainedInteriorReconstruction_closed_iff φ h3 hI (O_K.symm x) hyI).mp
    have hyoff := O_K.map_target hx
    rwa [hOKs] at hyoff

include hOKi hOLi hjL hρ in
theorem fibreRetainedInteriorPD_apply (x : K.Carrier)
    (hx : x ∈ (G.fibreRetainedInteriorPD φ h3 hI K O_K L O_L).source) :
    G.fibreRetainedInteriorPD φ h3 hI K O_K L O_L x = ρ (Quotient.mk'' x) := by
  apply hjL.injective
  have hnative := hx.1.2
  change O_K.symm x ∈ (G.retainedInteriorReconstructionPD φ h3 hI).source at hnative
  rw [G.retainedInteriorReconstructionPD_source] at hnative
  have he := hOLi (G.retainedInteriorReconstructionPD φ h3 hI (O_K.symm x)) hx.2
  change jL (O_L (G.retainedInteriorReconstructionPD φ h3 hI (O_K.symm x))) = _
  rw [he, G.retainedInteriorReconstructionPD_apply φ h3 hI _ hnative,
    G.retainedInverse_inclusion K ι O_K hOKi x hx.1.1, hρ]

def fibreRetainedInteriorImage : TopologicalSpace.Opens L.Carrier :=
  ⟨(G.fibreRetainedInteriorPD φ h3 hI K O_K L O_L).target,
    (G.fibreRetainedInteriorPD φ h3 hI K O_K L O_L).open_target⟩

include hι hK hboundary hOKs hOKt hOLs in
def fibreRetainedInteriorDiffeomorph :
    K.interior ≃ₘ⟮K.model, L.model⟯ G.fibreRetainedInteriorImage φ h3 hI K O_K L O_L := by
  let d := G.fibreRetainedInteriorPD φ h3 hI K O_K L O_L
  have hs : d.source = K.interior :=
    G.fibreRetainedInteriorPD_source φ h3 hI K ι hι hK hboundary O_K hOKs hOKt L O_L hOLs
  refine
    { toFun := fun x => ⟨d x.val, d.map_source (hs.symm ▸ x.property)⟩
      invFun := fun y => ⟨d.symm y.val, by
        have hx := d.map_target y.property
        rw [hs] at hx
        exact hx⟩
      left_inv := fun x => Subtype.ext (d.left_inv (hs.symm ▸ x.property))
      right_inv := fun y => Subtype.ext (d.right_inv y.property)
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    intro x
    exact (d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds
      (hs.symm ▸ x.property))).comp x contMDiff_subtype_val.contMDiffAt
  · apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    intro y
    exact (d.symm.contMDiffOn.contMDiffAt (d.open_target.mem_nhds
      y.property)).comp y contMDiff_subtype_val.contMDiffAt

include hι hK hboundary hOKs hOKt hOLs in
theorem fibreRetainedInteriorImage_subset :
    (G.fibreRetainedInteriorImage φ h3 hI K O_K L O_L : Set L.Carrier) ⊆ L.interior := by
  intro y hy
  let d := G.fibreRetainedInteriorPD φ h3 hI K O_K L O_L
  have hs : d.source = K.interior :=
    G.fibreRetainedInteriorPD_source φ h3 hI K ι hι hK hboundary O_K hOKs hOKt L O_L hOLs
  have hx : d.symm y ∈ d.source := d.map_target hy
  have hxI : d.symm y ∈ K.interior := by
    rwa [hs] at hx
  have hl := d.isLocalDiffeomorphAt K.model L.model ∞ hx
  have he := (hl.isInteriorPoint_iff (by simp)).mp hxI
  have hright : d (d.symm y) = y := d.right_inv hy
  change L.model.IsInteriorPoint (d (d.symm y)) at he
  rw [hright] at he
  exact he

theorem exists_fibreRetainedInterior
    {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
      (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
    (h3 : {p | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (hI : φ.target ⊆ G.cutCarrier.interior)
    (K : CompactCarrier.{u}) (ι : K.Carrier → G.cutCarrier.Carrier)
    (hι : _root_.Topology.IsEmbedding ι)
    (hK : range ι = G.FibreCutComplement φ)
    (hboundary : ι '' K.model.boundary K.Carrier =
      G.cutCarrier.model.boundary G.cutCarrier.Carrier ∪
        range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)))
    (O_K : PartialDiffeomorph G.cutCarrier.model K.model
      G.cutCarrier.Carrier K.Carrier ∞)
    (hOKs : O_K.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
    (hOKt : O_K.target = ι ⁻¹' (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
    (hOKi : ∀ x, x ∈ O_K.source → ι (O_K x) = x)
    (L : CompactCarrier.{u}) (jL : L.Carrier → W.Carrier)
    (hjL : _root_.Topology.IsEmbedding jL)
    (O_L : PartialDiffeomorph W.model L.model W.Carrier L.Carrier ∞)
    (hOLs : O_L.source = ((G.transportRegularFibreTube φ h3 hI) ''
      {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ)
    (hOLi : ∀ x, x ∈ O_L.source → jL (O_L x) = x)
    (ρ : Quotient (G.fibreRetainedGluing φ h3 hI K ι hι hK).setoid ≃ₜ L.Carrier)
    (hρ : ∀ x : K.Carrier,
      jL (ρ (Quotient.mk'' x)) = G.reconstruction (G.pairing.quotientMap (ι x))) :
    ∃ V : TopologicalSpace.Opens L.Carrier,
      ∃ e : K.interior ≃ₘ⟮K.model, L.model⟯ V,
        (∀ x : K.interior, (e x).val = ρ (Quotient.mk'' x.val)) ∧
        (V : Set L.Carrier) ⊆ L.interior
 := by
  refine ⟨G.fibreRetainedInteriorImage φ h3 hI K O_K L O_L,
    G.fibreRetainedInteriorDiffeomorph φ h3 hI K ι hι hK hboundary O_K hOKs hOKt L O_L hOLs,
    ?_, ?_⟩
  · intro x
    exact G.fibreRetainedInteriorPD_apply φ h3 hI K ι hι hK O_K hOKi L jL hjL O_L hOLi ρ hρ
      x.val (by
        rw [G.fibreRetainedInteriorPD_source φ h3 hI K ι hι hK hboundary O_K hOKs hOKt L O_L
          hOLs]
        exact x.property)
  · exact G.fibreRetainedInteriorImage_subset φ h3 hI K ι hι hK hboundary O_K hOKs hOKt L O_L
      hOLs

end GC.GraphManifold.RawGraphPresentation
