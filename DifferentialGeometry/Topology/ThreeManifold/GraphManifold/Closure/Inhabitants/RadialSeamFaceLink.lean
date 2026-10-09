import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialFaceIndex

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def radialSharedFace : radialRows.SharedFace := ⟨radialSharedEnd, by trivial⟩

theorem radial_shared_shape (σ : radialRows.SharedFace) : radialRows.sharedShape σ = .torus :=
  rfl

instance radialSharedSphereEmpty :
    IsEmpty {σ : radialRows.SharedFace // radialRows.sharedShape σ = .sphere} := by
  refine ⟨fun σ => ?_⟩
  have h := (radial_shared_shape σ.val).symm.trans σ.property
  cases h

def radialTorusSharedEquiv : Fin 1 ≃
    {σ : radialRows.SharedFace // radialRows.sharedShape σ = .torus} where
  toFun _ := ⟨radialSharedFace, rfl⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subtype.ext (radial_shared_indices_unique _ _)

def radialTorusOwner (b : Bool) : Fin 2 := if b then 1 else 0

def radialTorusFace (b : Bool) : ModelBoundaryFace (radialVertices.vertex
    (radialTorusOwner b)).piece := by
  cases b
  · exact cuspModelFace true
  · exact slimModelFace false

def radialTorusParam (b : Bool) : Torus →
    (radialVertices.vertex (radialTorusOwner b)).piece.Piece := by
  cases b
  · exact radialCuspSideParam
  · exact radialSlimSideParam

def radialSeamFaceLink : SeamFacesLink radialRows radialVertices radialVertexLink radialPorts
    radialSeams radialFaces radialSafe.shared where
  sphereEquiv := by
    change Fin 0 ≃ {σ : radialRows.SharedFace // radialRows.sharedShape σ = .sphere}
    exact Equiv.equivOfIsEmpty _ _
  torusEquiv := radialTorusSharedEquiv
  sphere_slim c := Fin.elim0 c
  sphere_neighbour c := Fin.elim0 c
  sphere_owner c := Fin.elim0 c
  sphereSideFace c := Fin.elim0 c
  sphereSideParam c := Fin.elim0 c
  sphereSideParam_embedding c := Fin.elim0 c
  sphereSideParam_range c := Fin.elim0 c
  sphereSide_map c := Fin.elim0 c
  sphere_closure c := Fin.elim0 c
  torusOwner _ b := radialTorusOwner b
  torusSide_eq _ _ := rfl
  torus_slim c := radialSharedCollar_zero.trans (radial_shared_level _).symm
  torus_neighbour c := by
    change range (fun t : Torus => radialSharedCollar (t, 0)) =
      cuspPiece.map '' (cuspModelFace true).val
    exact radialSharedCollar_zero.trans (radialCusp_model_image true).symm
  torus_owner c := ⟨true, rfl, rfl⟩
  torusSideFace _ b := radialTorusFace b
  torusSideParam _ b := radialTorusParam b
  torusSideParam_embedding c b := by
    cases b
    · exact radialCuspSideParam_embedding
    · exact radialSlimSideParam_embedding
  torusSideParam_range c b := by
    cases b
    · exact radialCuspSideParam_range
    · exact radialSlimSideParam_range
  torusSide_map c b t := by
    cases b
    · exact radialCuspSideParam_map t
    · exact radialSlimSideParam_map t
  torus_closure c := radialSharedCollar_closure_safe
  externalSideFace _ := cuspModelFace false
  externalSideFace_image i := by
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact (radialCusp_model_image false).trans radial_external_range.symm
  faceEquiv := radialFaceIndex
  faceEquiv_owner := radialFaceIndex_owner
  face_image := radialFaceIndex_image
  kind_sphere {f c b} := Fin.elim0 c
  kind_torus {f c b} := by
    have hc : c = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance c 0
    subst c
    cases b
    · change radialFaceKind f = .torusSeam (0 : Fin 1) false ↔
        radialFaceIndex f = radialFaceIndex (1 : Fin 4)
      constructor
      · intro hk
        fin_cases f
        · cases hk
        · rfl
        · cases hk
        · cases hk
      · intro he
        have hf := radialFaceIndex.injective he
        subst f
        rfl
    · change radialFaceKind f = .torusSeam (0 : Fin 1) true ↔
        radialFaceIndex f = radialFaceIndex (2 : Fin 4)
      constructor
      · intro hk
        fin_cases f
        · cases hk
        · cases hk
        · rfl
        · cases hk
      · intro he
        have hf := radialFaceIndex.injective he
        subst f
        rfl
  kind_external {f i} := by
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change radialFaceKind f = .external (0 : Fin 1) ↔
      radialFaceIndex f = radialFaceIndex (0 : Fin 4)
    constructor
    · intro hk
      fin_cases f
      · rfl
      · cases hk
      · cases hk
      · cases hk
    · intro he
      have hf := radialFaceIndex.injective he
      subst f
      rfl

end GC.GraphManifold.Assembly.FC39P0.X135Radial
