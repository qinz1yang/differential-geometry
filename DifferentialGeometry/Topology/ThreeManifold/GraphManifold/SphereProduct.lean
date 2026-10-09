import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Piece
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift

set_option autoImplicit false

/-!
# The sphere product as a graph manifold

A closed connected oriented three-manifold carrying a circle fibration over the whole carrier has
a raw graph presentation with a single piece, no torus pairing and no external tori:
`RawGraphPresentation.ofClosedCircleFibration`. The cut carrier is the carrier itself, the
pairing is `emptyTorusPairing`, and reconstruction, smoothness, orientation and interior data
are identities.

For `S² × S¹` (`sphereTwoTimesCircleLift`, charted on `EuclideanSpace ℝ (Fin 3)`) the circle
fibration is the first factor map read through `sphereTwoTimesCircleModelCopy.equiv.symm`,
over the base surface `sphereTwoSurface` (the unit sphere of `ℝ³`), with one global
trivialization: the product chart followed by the diffeomorphism
`sphereOneDiffeomorphCircle` from the unit sphere of `ℝ²` to `Circle`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Metric
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold
universe u

def BoundaryTori.empty (C : CompactCarrier.{u}) : BoundaryTori C 0 where
  collar i := i.elim0
  source_eq i := i.elim0
  boundary_zero i := i.elim0
  disjoint i := i.elim0

@[simp]
theorem BoundaryTori.empty_image (C : CompactCarrier.{u}) :
    (BoundaryTori.empty C).image = ∅ := by
  simp [BoundaryTori.image]

theorem closedCarrier_boundary_eq_empty (P : ConnectedClosedOrientedManifold.{u} 3) :
    (NoCuts.carrier P).model.boundary (NoCuts.carrier P).Carrier = ∅ := by
  change (𝓡 3).boundary P.Carrier = _
  exact ModelWithCorners.Boundaryless.boundary_eq_empty

namespace RawGraphPresentation

def ofClosedCircleFibration (P : ConnectedClosedOrientedManifold.{u} 3)
    (F : CircleFibration (NoCuts.carrier P) ⊤) : RawGraphPresentation (NoCuts.carrier P) where
  cutCarrier := NoCuts.carrier P
  components := NoCuts.components P
  fibration _ := F
  pairing := emptyTorusPairing _
  externalCount := 0
  external := BoundaryTori.empty _
  cutExternal := BoundaryTori.empty _
  external_exhausted := by
    rw [closedCarrier_boundary_eq_empty, BoundaryTori.empty_image]
  cut_boundary_exhausted := by
    rw [closedCarrier_boundary_eq_empty, BoundaryTori.empty_image, Set.union_empty,
      iUnion_block_emptyTorusPairing]
  external_disjoint := by
    rw [iUnion_block_emptyTorusPairing]
    exact Set.empty_disjoint _
  reconstruction := emptyTorusPairingHomeomorph _
  quotient_smooth := contMDiff_id
  quotient_oriented x := by
    refine ⟨LinearEquiv.refl ℝ _, fun v => ?_, ?_⟩
    · change v = mfderiv _ _ (id : P.Carrier → P.Carrier) x v
      rw [mfderiv_id]
      rfl
    · exact Equiv.congr_fun (Orientation.map_refl (Fin 3)) _
  interiorImage := (NoCuts.carrier P).interior
  interiorDiffeomorph := Diffeomorph.refl _ _ ∞
  interior_map _ := rfl
  seam i := i.elim0
  seam_source i := i.elim0
  seam_zero i := i.elim0
  seam_positive i := i.elim0
  seam_negative i := i.elim0
  seam_interior i := i.elim0
  seam_disjoint i := i.elim0
  marked_collar i := i.elim0
  external_seam_disjoint i := i.elim0
  leftPiece i := i.elim0
  rightPiece i := i.elim0
  left_owned i := i.elim0
  right_owned i := i.elim0
  externalPiece i := i.elim0
  external_owned i := i.elim0

variable (P : ConnectedClosedOrientedManifold.{u} 3) (F : CircleFibration (NoCuts.carrier P) ⊤)

@[simp]
theorem ofClosedCircleFibration_components_count :
    (ofClosedCircleFibration P F).components.count = 1 := rfl

@[simp]
theorem ofClosedCircleFibration_pairing_count :
    (ofClosedCircleFibration P F).pairing.count = 0 := rfl

@[simp]
theorem ofClosedCircleFibration_externalCount :
    (ofClosedCircleFibration P F).externalCount = 0 := rfl

theorem ofClosedCircleFibration_fibration (i : Fin (ofClosedCircleFibration P F).components.count) :
    (ofClosedCircleFibration P F).fibration i = F := rfl

end RawGraphPresentation

local instance : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private abbrev planeComplex : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

private theorem planeComplex_mem_sphere (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    planeComplex x ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
  exact norm_eq_of_mem_sphere x

private theorem planeComplex_symm_mem_sphere (z : sphere (0 : ℂ) 1) :
    planeComplex.symm z ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
  exact norm_eq_of_mem_sphere z

def sphereOneDiffeomorphCircle :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toFun x := ⟨planeComplex x, planeComplex_mem_sphere x⟩
  invFun z := ⟨planeComplex.symm z, planeComplex_symm_mem_sphere z⟩
  left_inv x := Subtype.ext (planeComplex.symm_apply_apply x.val)
  right_inv z := Subtype.ext (planeComplex.apply_symm_apply (z : ℂ))
  contMDiff_toFun :=
    (planeComplex.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere
      planeComplex_mem_sphere
  contMDiff_invFun :=
    (planeComplex.symm.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere
      planeComplex_symm_mem_sphere

private theorem connectedSpace_sphereTwo :
    ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num))

def sphereTwoSurface : CompactSurface.{0} where
  kind := .closed
  Carrier := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  charts := inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 2)) _)
  smooth := inferInstanceAs (IsManifold (𝓡 2) ∞ (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
  connected := connectedSpace_sphereTwo

private def univOpensDiffeomorph {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (U : TopologicalSpace.Opens M)
    (h : ∀ x : M, x ∈ U) : U ≃ₘ⟮𝓡 3, 𝓡 3⟯ M where
  toFun := Subtype.val
  invFun x := ⟨x, h x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U _).mp contMDiff_id

private abbrev productChart :
    sphereTwoTimesCircleLift.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯
      SphereTwoTimesCircle :=
  sphereTwoTimesCircleModelCopy.equiv.symm

def sphereTwoTimesCircleProjection :
    C((⊤ : TopologicalSpace.Opens (NoCuts.carrier sphereTwoTimesCircleLift).Carrier),
      sphereTwoSurface.Carrier) :=
  ⟨fun x => (productChart x.val).1,
    continuous_fst.comp (productChart.continuous.comp continuous_subtype_val)⟩

def sphereTwoTimesCircleCircleFibration :
    CircleFibration (NoCuts.carrier sphereTwoTimesCircleLift) ⊤ where
  base := sphereTwoSurface
  projection := sphereTwoTimesCircleProjection
  surjective b := ⟨⟨productChart.symm (b, sphereOneDiffeomorphCircle.symm 1), trivial⟩, by
    change (productChart (productChart.symm _)).1 = b
    rw [Diffeomorph.apply_symm_apply]⟩
  smooth := contMDiff_fst.comp (productChart.contMDiff.comp contMDiff_subtype_val)
  neighborhood _ := ⊤
  mem_neighborhood _ := trivial
  trivialization _ :=
    (univOpensDiffeomorph (TopologicalSpace.Opens.comap sphereTwoTimesCircleProjection ⊤)
        (fun _ => trivial)).trans
      ((topOpensDiffeomorph (I := 𝓡 3)
          (NoCuts.carrier sphereTwoTimesCircleLift).Carrier).trans
        (productChart.trans
          ((topOpensDiffeomorph (I := 𝓡 2)
              (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).symm.prodCongr
            sphereOneDiffeomorphCircle)))
  projection_trivialization _ _ := rfl

@[simp]
theorem sphereTwoTimesCircleCircleFibration_base :
    sphereTwoTimesCircleCircleFibration.base = sphereTwoSurface := rfl

theorem sphereTwoTimesCircleProjection_apply
    (x : (⊤ : TopologicalSpace.Opens (NoCuts.carrier sphereTwoTimesCircleLift).Carrier)) :
    sphereTwoTimesCircleProjection x = (sphereTwoTimesCircleModelCopy.equiv.symm x.val).1 :=
  rfl

def sphereTwoTimesCircleRawGraphPresentation :
    RawGraphPresentation (NoCuts.carrier sphereTwoTimesCircleLift) :=
  RawGraphPresentation.ofClosedCircleFibration _ sphereTwoTimesCircleCircleFibration

end GC.GraphManifold
