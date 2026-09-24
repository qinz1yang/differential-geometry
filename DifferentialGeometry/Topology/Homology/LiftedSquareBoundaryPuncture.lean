import DifferentialGeometry.Topology.Homology.LiftedSquareBoundaryDegree
import DifferentialGeometry.Topology.Homology.SquareBoundaryPunctured

noncomputable section

open Set ContinuousMap
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

def liftedSquareBoundaryPuncture : Set (liftedSquare.{u}) :=
  liftedSquareBoundary.{u} \ {ULift.up squareNorthEast}

def liftedSquareBoundaryOriginPuncture : Set (liftedSquare.{u}) :=
  liftedSquareBoundary.{u} \ {ULift.up squareOrigin}

def liftedSquareBoundaryHomeomorph :
    ↥(liftedSquareBoundary.{u}) ≃ₜ ↥(Cube.boundary (Fin 2) : Set Square) where
  toFun x := ⟨x.val.down, x.property⟩
  invFun t := ⟨ULift.up t.val, t.property⟩
  left_inv x := Subtype.ext (ULift.ext x.val (ULift.up x.val.down) rfl).symm
  right_inv := fun _ => Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_uliftDown.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_uliftUp.comp continuous_subtype_val) _

def liftedSquareBoundaryPunctureHomeomorph :
    ↥(liftedSquareBoundaryPuncture.{u}) ≃ₜ ↥squareBoundaryPuncture where
  toFun x := ⟨x.val.down, x.property.1,
    fun h => x.property.2 (ULift.ext x.val (ULift.up squareNorthEast) h)⟩
  invFun t := ⟨ULift.up t.val, t.property.1,
    fun h => t.property.2 (congrArg ULift.down h)⟩
  left_inv x := Subtype.ext (ULift.ext x.val (ULift.up x.val.down) rfl).symm
  right_inv := fun _ => Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_uliftDown.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_uliftUp.comp continuous_subtype_val) _

def liftedSquareBoundaryOriginPunctureHomeomorph :
    ↥(liftedSquareBoundaryOriginPuncture.{u}) ≃ₜ ↥squareBoundaryOriginPuncture where
  toFun x := ⟨x.val.down, x.property.1,
    fun h => x.property.2 (ULift.ext x.val (ULift.up squareOrigin) h)⟩
  invFun t := ⟨ULift.up t.val, t.property.1,
    fun h => t.property.2 (congrArg ULift.down h)⟩
  left_inv x := Subtype.ext (ULift.ext x.val (ULift.up x.val.down) rfl).symm
  right_inv := fun _ => Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_uliftDown.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_uliftUp.comp continuous_subtype_val) _

theorem liftedSquareBoundaryPuncture_contractible :
    ContractibleSpace ↥(liftedSquareBoundaryPuncture.{u}) :=
  haveI := squareBoundaryPuncture_contractible
  liftedSquareBoundaryPunctureHomeomorph.contractibleSpace

theorem liftedSquareBoundaryOriginPuncture_contractible :
    ContractibleSpace ↥(liftedSquareBoundaryOriginPuncture.{u}) :=
  haveI := squareBoundaryOriginPuncture_contractible
  liftedSquareBoundaryOriginPunctureHomeomorph.contractibleSpace

theorem squareEast_mem_liftedSquareBoundaryPuncture :
    (ULift.up squareEast : liftedSquare.{u}) ∈ liftedSquareBoundaryPuncture :=
  ⟨squareEast_mem_boundary, fun h => squareEast_ne_northEast (congrArg ULift.down h)⟩

theorem squareNorth_mem_liftedSquareBoundaryOriginPuncture :
    (ULift.up squareNorth : liftedSquare.{u}) ∈ liftedSquareBoundaryOriginPuncture :=
  ⟨squareNorth_mem_boundary, fun h => squareNorth_ne_origin (congrArg ULift.down h)⟩

theorem liftedSquareBoundaryPuncture_nonempty :
    (liftedSquareBoundaryPuncture.{u}).Nonempty :=
  ⟨ULift.up squareEast, squareEast_mem_liftedSquareBoundaryPuncture⟩

theorem liftedSquareBoundaryOriginPuncture_nonempty :
    (liftedSquareBoundaryOriginPuncture.{u}).Nonempty :=
  ⟨ULift.up squareNorth, squareNorth_mem_liftedSquareBoundaryOriginPuncture⟩

theorem liftedSquareBoundary_eq_punctures_union :
    liftedSquareBoundaryPuncture.{u} ∪ liftedSquareBoundaryOriginPuncture.{u} =
      liftedSquareBoundary.{u} := by
  ext x
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1
  · intro hx
    by_cases h : x = ULift.up squareNorthEast
    · subst h
      exact Or.inr ⟨hx, fun hh => squareNorthEast_ne_origin (congrArg ULift.down hh)⟩
    · exact Or.inl ⟨hx, h⟩

end DifferentialGeometry.Topology
