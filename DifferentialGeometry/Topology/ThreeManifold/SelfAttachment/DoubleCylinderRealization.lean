import DifferentialGeometry.Topology.Attachment.AdjunctionHomeomorph
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderMappingTorus

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.DoubleCylinder

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
  (a c : Cylinder → M) (ha : Continuous a) (hc : Continuous c)
  (hai : Injective a) (hci : Injective c)
  (hcover : range a ∪ range c = univ)
  (hcross : ∀ p q, a p = c q ↔ ∃ z : Bool × SphereTwo,
    SelfAttachment.boundaryInclusion z = p ∧ attachingMap f z = q)

def ambientHomeomorph : Space f ≃ₜ M := by
  have hsurj : Surjective (Sum.elim a c) := by
    intro y
    have hy : y ∈ range a ∪ range c := hcover.symm ▸ mem_univ y
    rcases hy with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact ⟨Sum.inl p, rfl⟩
    · exact ⟨Sum.inr q, rfl⟩
  have hquot : _root_.Topology.IsQuotientMap (Sum.elim a c) :=
    _root_.Topology.IsQuotientMap.of_surjective_continuous hsurj
      (continuous_sum_dom.mpr ⟨ha, hc⟩)
  exact adjunctionHomeomorphOfFibers SelfAttachment.boundaryInclusion (attachingMap f)
    (Sum.elim a c) hquot hai hci hcross

@[simp] theorem ambientHomeomorph_mk (p : Cylinder ⊕ Cylinder) :
    ambientHomeomorph f a c ha hc hai hci hcover hcross
      (adjunctionMk SelfAttachment.boundaryInclusion (attachingMap f) p) = Sum.elim a c p := rfl

@[simp] theorem ambientHomeomorph_band (p : Cylinder) :
    ambientHomeomorph f a c ha hc hai hci hcover hcross (band f p) = a p := rfl

@[simp] theorem ambientHomeomorph_core (p : Cylinder) :
    ambientHomeomorph f a c ha hc hai hci hcover hcross (core f p) = c p := rfl

def ambientMappingTorusHomeomorph : M ≃ₜ SphereMappingTorus f :=
  (ambientHomeomorph f a c ha hc hai hci hcover hcross).symm.trans (mappingTorusHomeomorph f)

@[simp] theorem ambientMappingTorusHomeomorph_band (p : Cylinder) :
    ambientMappingTorusHomeomorph f a c ha hc hai hci hcover hcross (a p) =
      bandToMappingTorus f p := by
  change mappingTorusHomeomorph f
    ((ambientHomeomorph f a c ha hc hai hci hcover hcross).symm (a p)) = _
  rw [← ambientHomeomorph_band f a c ha hc hai hci hcover hcross p,
    Homeomorph.symm_apply_apply]
  rfl

@[simp] theorem ambientMappingTorusHomeomorph_core (p : Cylinder) :
    ambientMappingTorusHomeomorph f a c ha hc hai hci hcover hcross (c p) =
      coreToMappingTorus f p := by
  change mappingTorusHomeomorph f
    ((ambientHomeomorph f a c ha hc hai hci hcover hcross).symm (c p)) = _
  rw [← ambientHomeomorph_core f a c ha hc hai hci hcover hcross p,
    Homeomorph.symm_apply_apply]
  rfl

end DifferentialGeometry.Topology.DoubleCylinder


set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.DoubleCylinder

variable {M : Type*}
  (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (a c : Cylinder → M)
  (hai : Injective a) (hci : Injective c)
  (hinter : range a ∩ range c ⊆
    range (fun z => c (z, ⟨0, by norm_num⟩)) ∪
      range (fun z => c (z, ⟨1, by norm_num⟩)))
  (hzero : ∀ z, a (z, ⟨0, by norm_num⟩) = c (z, ⟨0, by norm_num⟩))
  (hone : ∀ z, a (z, ⟨1, by norm_num⟩) = c (f.symm z, ⟨1, by norm_num⟩))

include hai hci hinter hzero hone in
theorem band_eq_core_iff_of_boundary_eq (p q : Cylinder) :
    a p = c q ↔ ∃ z : Bool × SphereTwo,
      SelfAttachment.boundaryInclusion z = p ∧ attachingMap f z = q := by
  constructor
  · intro hpq
    have hm : a p ∈ range a ∩ range c := ⟨⟨p, rfl⟩, ⟨q, hpq.symm⟩⟩
    rcases hinter hm with ⟨z, hz⟩ | ⟨z, hz⟩
    · refine ⟨(false, z), hai ((hzero z).trans hz), hci (hz.trans hpq)⟩
    · refine ⟨(true, f z), ?_, ?_⟩
      · apply hai
        change a (f z, ⟨1, by norm_num⟩) = a p
        rw [hone, f.symm_apply_apply]
        exact hz
      · apply hci
        change c (f.symm (f z), ⟨1, by norm_num⟩) = c q
        rw [f.symm_apply_apply]
        exact hz.trans hpq
  · rintro ⟨⟨b, z⟩, rfl, rfl⟩
    cases b
    · exact hzero z
    · exact hone z

variable [TopologicalSpace M] [T2Space M]
  (ha : Continuous a) (hc : Continuous c) (hcover : range a ∪ range c = univ)

def ambientMappingTorusHomeomorphOfBoundaryEquations : M ≃ₜ SphereMappingTorus f :=
  ambientMappingTorusHomeomorph f a c ha hc hai hci hcover
    (band_eq_core_iff_of_boundary_eq f a c hai hci hinter hzero hone)

@[simp] theorem ambientMappingTorusHomeomorphOfBoundaryEquations_band (p : Cylinder) :
    ambientMappingTorusHomeomorphOfBoundaryEquations f a c hai hci hinter hzero hone
      ha hc hcover (a p) = bandToMappingTorus f p :=
  ambientMappingTorusHomeomorph_band f a c ha hc hai hci hcover _ p

@[simp] theorem ambientMappingTorusHomeomorphOfBoundaryEquations_core (p : Cylinder) :
    ambientMappingTorusHomeomorphOfBoundaryEquations f a c hai hci hinter hzero hone
      ha hc hcover (c p) = coreToMappingTorus f p :=
  ambientMappingTorusHomeomorph_core f a c ha hc hai hci hcover _ p

end DifferentialGeometry.Topology.DoubleCylinder
