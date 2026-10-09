import DifferentialGeometry.Topology.ThreeManifold.UncappingReparametrization

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "Annulus" => Sphere × Icc (1 / 4 : ℝ) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

def uncappingProjection :
    C(((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier),
      C.UncappingQuotient) where
  toFun x := Quot.mk C.innerCapRelation (C.puncturedCappingHomeomorph.symm x)
  continuous_toFun := continuous_quot_mk.comp C.puncturedCappingHomeomorph.symm.continuous

@[simp] theorem uncappingProjection_homeomorph (x : C.PuncturedCapping) :
    C.uncappingProjection (C.puncturedCappingHomeomorph x) = Quot.mk C.innerCapRelation x := by
  change Quot.mk C.innerCapRelation (C.puncturedCappingHomeomorph.symm
    (C.puncturedCappingHomeomorph x)) = _
  rw [Homeomorph.symm_apply_apply]

theorem uncappingProjection_core (x : T.core) :
    C.uncappingProjection (C.puncturedCappingHomeomorph (adjunctionLower
      (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) =
      Quot.mk C.innerCapRelation (adjunctionLower
        (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
          (C.coreImageHomeomorph x)) :=
  C.uncappingProjection_homeomorph _

theorem uncappingProjection_of_eq_coreInclusion (x : T.core)
    (y : ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier))
    (hy : y.val = C.coreInclusion x) :
    C.uncappingProjection y = Quot.mk C.innerCapRelation (adjunctionLower
      (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x)) := by
  have heq : C.puncturedCappingHomeomorph (adjunctionLower
      (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x)) = y := Subtype.ext hy.symm
  rw [← heq, C.uncappingProjection_core]

theorem uncappingProjection_annulus (b : T.Boundary) (q : Annulus)
    (x : ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier))
    (hx : x.val = C.capAnnulusMap b q) :
    C.uncappingProjection x = Quot.mk C.innerCapRelation (adjunctionCell
      (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap ⟨b, q⟩) := by
  have heq : C.puncturedCappingHomeomorph (adjunctionCell
      (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap ⟨b, q⟩) = x :=
    Subtype.ext hx.symm
  rw [← heq, C.uncappingProjection_homeomorph]

def puncturedCapBoundary (b : T.Boundary) (z : Sphere) :
    ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier) :=
  C.puncturedCappingHomeomorph (C.innerCapBoundary b.1 b.2 (if b.2 then z else -z))

theorem puncturedCapBoundary_val (b : T.Boundary) (z : Sphere) :
    (C.puncturedCapBoundary b z).val = ((C.capBallChart b).toBallChart.boundaryMap z).val := by
  change C.capAnnulusMap b ((if b.2 then z else -z), ⟨1 / 4, by norm_num⟩) = _
  rw [C.capAnnulusMap_inner]
  cases b.2 <;> simp

theorem uncappingProjection_boundary (b : T.Boundary) (z : Sphere) :
    C.uncappingProjection (C.puncturedCapBoundary b z) =
      Quot.mk C.innerCapRelation (C.innerCapBoundary b.1 b.2 (if b.2 then z else -z)) :=
  C.uncappingProjection_homeomorph _

theorem uncappingProjection_boundary_antipodal (a : T.Index) (z : Sphere) :
    C.uncappingProjection (C.puncturedCapBoundary (a, false) z) =
      C.uncappingProjection (C.puncturedCapBoundary (a, true) (-z)) := by
  rw [C.uncappingProjection_boundary, C.uncappingProjection_boundary]
  exact Quot.sound ⟨a, -z, Or.inl ⟨rfl, rfl⟩⟩

variable (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3)
  (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
  (hboundary : ∀ b (z : Sphere), B b (sphereToClosedCell z) = sphereToClosedCell z)

theorem uncappingProjection_reparametrization
    (x : ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier)) :
    C.uncappingProjection (C.puncturedCappingComplementReparametrization B hsmall hboundary x) =
      C.uncappingQuotientReparametrization B hsmall hboundary (C.uncappingProjection x) := by
  obtain ⟨y, rfl⟩ := C.puncturedCappingHomeomorph.surjective x
  rw [C.puncturedCappingComplementReparametrization_homeomorph,
    C.uncappingProjection_homeomorph, C.uncappingProjection_homeomorph,
    C.uncappingQuotientReparametrization_mk]

theorem uncappingProjection_cap_reparametrization (b : T.Boundary) (q : Annulus)
    (x : ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier))
    (hx : x.val = C.cap b (B b ⟨q.2.val • q.1.val, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [q.2.property.1]),
        norm_eq_of_mem_sphere, mul_one]
      exact q.2.property.2⟩)) :
    C.uncappingProjection x = C.uncappingQuotientReparametrization B hsmall hboundary
      (Quot.mk C.innerCapRelation (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap ⟨b, q⟩)) := by
  have hx' : x.val = C.capAnnulusMap b (C.capAnnulusHomeomorph b (B b) (hsmall b) q) :=
    hx.trans (C.capAnnulusHomeomorph_apply b (B b) (hsmall b) q).symm
  rw [C.uncappingProjection_annulus b _ x hx', C.uncappingQuotientReparametrization_annulus]

end DifferentialGeometry.Topology.SphericalCapping
