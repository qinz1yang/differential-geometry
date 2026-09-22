import DifferentialGeometry.Topology.ThreeManifold.PuncturedUncapping
import DifferentialGeometry.Topology.ThreeManifold.PuncturedCappingReparametrization

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "Sphere" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Annulus" => Sphere × Icc (1 / 4 : ℝ) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)
  (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3)
  (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
  (hboundary : ∀ b (z : Sphere), B b (sphereToClosedCell z) = sphereToClosedCell z)

theorem puncturedCappingReparametrization_innerCapBoundary
    (a : T.Index) (side : Bool) (z : Sphere) :
    C.puncturedCappingReparametrization B hsmall hboundary (C.innerCapBoundary a side z) =
      C.innerCapBoundary a side z :=
  C.puncturedCappingReparametrization_inner B hsmall hboundary (a, side) z

theorem puncturedCappingReparametrization_innerCapRelation_iff (x y : C.PuncturedCapping) :
    C.innerCapRelation (C.puncturedCappingReparametrization B hsmall hboundary x)
        (C.puncturedCappingReparametrization B hsmall hboundary y) ↔
      C.innerCapRelation x y := by
  let H := C.puncturedCappingReparametrization B hsmall hboundary
  have hf (a : T.Index) (side : Bool) (z : Sphere) :
      H (C.innerCapBoundary a side z) = C.innerCapBoundary a side z :=
    C.puncturedCappingReparametrization_innerCapBoundary B hsmall hboundary a side z
  constructor
  · rintro ⟨a, z, h | h⟩
    · exact ⟨a, z, Or.inl ⟨H.injective (h.1.trans (hf a false z).symm),
        H.injective (h.2.trans (hf a true z).symm)⟩⟩
    · exact ⟨a, z, Or.inr ⟨H.injective (h.1.trans (hf a false z).symm),
        H.injective (h.2.trans (hf a true z).symm)⟩⟩
  · rintro ⟨a, z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨a, z, Or.inl ⟨hf a false z, hf a true z⟩⟩
    · exact ⟨a, z, Or.inr ⟨hf a false z, hf a true z⟩⟩

def uncappingQuotientReparametrization : C.UncappingQuotient ≃ₜ C.UncappingQuotient :=
  Homeomorph.Quot.congr (C.puncturedCappingReparametrization B hsmall hboundary)
    (fun x y => (C.puncturedCappingReparametrization_innerCapRelation_iff B hsmall hboundary x y).symm)

@[simp] theorem uncappingQuotientReparametrization_mk (x : C.PuncturedCapping) :
    C.uncappingQuotientReparametrization B hsmall hboundary (Quot.mk C.innerCapRelation x) =
      Quot.mk C.innerCapRelation (C.puncturedCappingReparametrization B hsmall hboundary x) := rfl

@[simp] theorem uncappingQuotientReparametrization_symm_mk (x : C.PuncturedCapping) :
    (C.uncappingQuotientReparametrization B hsmall hboundary).symm (Quot.mk C.innerCapRelation x) =
      Quot.mk C.innerCapRelation ((C.puncturedCappingReparametrization B hsmall hboundary).symm x) := rfl

theorem uncappingQuotientReparametrization_core (x : range C.coreInclusion) :
    C.uncappingQuotientReparametrization B hsmall hboundary
      (Quot.mk C.innerCapRelation (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap x)) =
      Quot.mk C.innerCapRelation (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap x) := rfl

theorem uncappingQuotientReparametrization_symm_core (x : range C.coreInclusion) :
    (C.uncappingQuotientReparametrization B hsmall hboundary).symm
      (Quot.mk C.innerCapRelation (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap x)) =
      Quot.mk C.innerCapRelation (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap x) := rfl

theorem uncappingQuotientReparametrization_annulus (b : T.Boundary) (q : Annulus) :
    C.uncappingQuotientReparametrization B hsmall hboundary
      (Quot.mk C.innerCapRelation (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap ⟨b, q⟩)) =
      Quot.mk C.innerCapRelation (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap ⟨b, C.capAnnulusHomeomorph b (B b) (hsmall b) q⟩) := rfl

theorem uncappingQuotientReparametrization_inner (a : T.Index) (side : Bool) (z : Sphere) :
    C.uncappingQuotientReparametrization B hsmall hboundary
      (Quot.mk C.innerCapRelation (C.innerCapBoundary a side z)) =
      Quot.mk C.innerCapRelation (C.innerCapBoundary a side z) := by
  rw [C.uncappingQuotientReparametrization_mk,
    C.puncturedCappingReparametrization_innerCapBoundary]

theorem uncappingQuotientReparametrization_symm_inner (a : T.Index) (side : Bool) (z : Sphere) :
    (C.uncappingQuotientReparametrization B hsmall hboundary).symm
      (Quot.mk C.innerCapRelation (C.innerCapBoundary a side z)) =
      Quot.mk C.innerCapRelation (C.innerCapBoundary a side z) := by
  apply (C.uncappingQuotientReparametrization B hsmall hboundary).injective
  rw [Homeomorph.apply_symm_apply, C.uncappingQuotientReparametrization_inner]

end DifferentialGeometry.Topology.SphericalCapping
