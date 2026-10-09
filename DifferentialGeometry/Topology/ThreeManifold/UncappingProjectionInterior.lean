import DifferentialGeometry.Topology.ThreeManifold.UncappingLocalMap

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1

private theorem eq_of_eqvGen_of_no_relation {X : Type*} {r : X → X → Prop} {x y : X}
    (hl : ∀ z, ¬ r x z) (hr : ∀ z, ¬ r z x) (h : Relation.EqvGen r x y) : x = y := by
  have hm : ∀ {a b : X}, Relation.EqvGen r a b → (a = x ↔ b = x) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      constructor
      · intro ha
        subst a
        exact (hl b hab).elim
      · intro hb
        subst b
        exact (hr a hab).elim
    | refl => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ihab ihbc => exact ihab.trans ihbc
  exact ((hm h).mp rfl).symm

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem interior_preimage_ne_innerCapBoundary (x : C.uncappingInterior)
    (a : T.Index) (side : Bool) (z : Sphere) :
    C.puncturedCappingHomeomorph.symm (C.uncappingInteriorInclusion x) ≠
      C.innerCapBoundary a side z := by
  intro h
  have hv := congrArg (fun q : C.PuncturedCapping => (C.puncturedCappingHomeomorph q).val) h
  rw [Homeomorph.apply_symm_apply] at hv
  change x.val = C.capAnnulusMap (a, side) (z, ⟨1 / 4, by norm_num⟩) at hv
  rw [C.capAnnulusMap_inner] at hv
  apply x.property
  refine mem_iUnion.mpr ⟨(a, side), (if side then z else -z).val, ?_, hv.symm⟩
  rw [mem_closedBall_zero_iff, norm_eq_of_mem_sphere]

private theorem interior_preimage_not_related (x : C.uncappingInterior) (y : C.PuncturedCapping) :
    ¬ C.innerCapRelation
      (C.puncturedCappingHomeomorph.symm (C.uncappingInteriorInclusion x)) y := by
  rintro ⟨a, z, h | h⟩
  · exact C.interior_preimage_ne_innerCapBoundary x a false z h.1
  · exact C.interior_preimage_ne_innerCapBoundary x a true z h.2

private theorem not_related_interior_preimage (x : C.uncappingInterior) (y : C.PuncturedCapping) :
    ¬ C.innerCapRelation y
      (C.puncturedCappingHomeomorph.symm (C.uncappingInteriorInclusion x)) := by
  rintro ⟨a, z, h | h⟩
  · exact C.interior_preimage_ne_innerCapBoundary x a true z h.2
  · exact C.interior_preimage_ne_innerCapBoundary x a false z h.1

theorem uncappingProjection_injective_on_interior :
    Function.Injective (fun y : C.uncappingInterior =>
      C.uncappingProjection (C.uncappingInteriorInclusion y)) := by
  intro x y h
  have hq : C.puncturedCappingHomeomorph.symm (C.uncappingInteriorInclusion x) =
      C.puncturedCappingHomeomorph.symm (C.uncappingInteriorInclusion y) :=
    eq_of_eqvGen_of_no_relation (C.interior_preimage_not_related x)
      (C.not_related_interior_preimage x) (Quot.eqvGen_exact h)
  have hi : C.uncappingInteriorInclusion x = C.uncappingInteriorInclusion y :=
    C.puncturedCappingHomeomorph.symm.injective hq
  exact Subtype.ext (congrArg (fun p :
    ((⋃ b, (C.capBallChart b).chart '' ball (0 : E3) 1)ᶜ : Set N.Carrier) => p.val) hi)

end DifferentialGeometry.Topology.SphericalCapping
