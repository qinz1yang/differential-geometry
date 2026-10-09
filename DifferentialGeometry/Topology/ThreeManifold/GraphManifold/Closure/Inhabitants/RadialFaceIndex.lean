import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialFaceLayer

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
attribute [local instance] Classical.propDecidable

theorem radial_cusp_faces_ne : cuspModelFace false ≠ cuspModelFace true := by
  intro he
  have hv : range (cuspEnd false) = range (cuspEnd true) := congrArg Subtype.val he
  have hp : cuspEnd false (1, 1) ∈ range (cuspEnd true) := hv ▸ mem_range_self (1, 1)
  rw [cuspEnd_range true] at hp
  change cliffordHeight (cuspEnd false (1, 1)).val = -(1 / 4 : ℝ) at hp
  have hh := cuspEnd_height false (1, 1)
  change cliffordHeight (cuspEnd false (1, 1)).val = 0 at hh
  linarith

theorem radial_slim_faces_ne : slimModelFace false ≠ slimModelFace true := by
  intro he
  have hv : range (slimEnd false) = range (slimEnd true) := congrArg Subtype.val he
  have hp : slimEnd false (1, 1) ∈ range (slimEnd true) := hv ▸ mem_range_self (1, 1)
  rw [slimEnd_range true] at hp
  change cliffordHeight (slimEnd false (1, 1)).val = -(1 / 2 : ℝ) at hp
  have hh := slimEnd_height false (1, 1)
  change cliffordHeight (slimEnd false (1, 1)).val = -(1 / 4 : ℝ) at hh
  linarith

def radialCuspModelEquiv : Bool ≃ ModelBoundaryFace cuspPiece where
  toFun := cuspModelFace
  invFun F := if F = cuspModelFace false then false else true
  left_inv b := by
    cases b
    · simp
    · simp [Ne.symm radial_cusp_faces_ne]
  right_inv F := by
    rcases cuspModelFace_cases F with h | h
    · subst F
      simp
    · subst F
      simp [Ne.symm radial_cusp_faces_ne]

def radialSlimModelEquiv : Bool ≃ ModelBoundaryFace slimPiece where
  toFun := slimModelFace
  invFun F := if F = slimModelFace false then false else true
  left_inv b := by
    cases b
    · simp
    · simp [Ne.symm radial_slim_faces_ne]
  right_inv F := by
    rcases slimModelFace_cases F with h | h
    · subst F
      simp
    · subst F
      simp [Ne.symm radial_slim_faces_ne]

def radialFacePair : Fin 4 ≃ (Fin 2 × Bool) where
  toFun f := if f = 0 then (0, false) else if f = 1 then (0, true) else
    if f = 2 then (1, false) else (1, true)
  invFun q := if q.1 = 0 then (if q.2 then 1 else 0) else (if q.2 then 3 else 2)
  left_inv f := by fin_cases f <;> rfl
  right_inv q := by rcases q with ⟨v, b⟩; fin_cases v <;> cases b <;> rfl

def radialModelFacePair : (Fin 2 × Bool) ≃
    (Σ v : Fin 2, ModelBoundaryFace (radialVertices.vertex v).piece) where
  toFun q := by
    rcases q with ⟨v, b⟩
    by_cases hv : v = 0
    · subst v
      exact ⟨(0 : Fin 2), radialCuspModelEquiv b⟩
    · have h1 : v = 1 := by omega
      subst v
      exact ⟨(1 : Fin 2), radialSlimModelEquiv b⟩
  invFun q := by
    rcases q with ⟨v, F⟩
    by_cases hv : v = 0
    · subst v
      exact ((0 : Fin 2), radialCuspModelEquiv.symm F)
    · have h1 : v = 1 := by omega
      subst v
      exact ((1 : Fin 2), radialSlimModelEquiv.symm F)
  left_inv q := by
    rcases q with ⟨v, b⟩
    fin_cases v
    · change ((0 : Fin 2), radialCuspModelEquiv.symm (radialCuspModelEquiv b)) = (0, b)
      rw [radialCuspModelEquiv.symm_apply_apply]
    · change ((1 : Fin 2), radialSlimModelEquiv.symm (radialSlimModelEquiv b)) = (1, b)
      rw [radialSlimModelEquiv.symm_apply_apply]
  right_inv q := by
    rcases q with ⟨v, F⟩
    fin_cases v
    · change @Sigma.mk (Fin 2) (fun v => ModelBoundaryFace (radialVertices.vertex v).piece)
        0 (radialCuspModelEquiv (radialCuspModelEquiv.symm F)) =
        @Sigma.mk (Fin 2) (fun v => ModelBoundaryFace (radialVertices.vertex v).piece) 0 F
      have he := radialCuspModelEquiv.apply_symm_apply (show ModelBoundaryFace cuspPiece from F)
      exact congrArg (fun m : ModelBoundaryFace cuspPiece =>
        @Sigma.mk (Fin 2) (fun v => ModelBoundaryFace (radialVertices.vertex v).piece) 0 m) he
    · change @Sigma.mk (Fin 2) (fun v => ModelBoundaryFace (radialVertices.vertex v).piece)
        1 (radialSlimModelEquiv (radialSlimModelEquiv.symm F)) =
        @Sigma.mk (Fin 2) (fun v => ModelBoundaryFace (radialVertices.vertex v).piece) 1 F
      have he := radialSlimModelEquiv.apply_symm_apply (show ModelBoundaryFace slimPiece from F)
      exact congrArg (fun m : ModelBoundaryFace slimPiece =>
        @Sigma.mk (Fin 2) (fun v => ModelBoundaryFace (radialVertices.vertex v).piece) 1 m) he

def radialFaceIndex : Fin 4 ≃
    (Σ v : Fin 2, ModelBoundaryFace (radialVertices.vertex v).piece) :=
  radialFacePair.trans radialModelFacePair

theorem radialFaceIndex_owner (f : Fin 4) : (radialFaceIndex f).1 = radialFaceOwner f := by
  fin_cases f <;> rfl

theorem radialCusp_model_image (b : Bool) : cuspPiece.map '' (cuspModelFace b).val =
    {p | height p = if b then -(1 / 4 : ℝ) else 0} := by
  change cuspToCarrier '' range (cuspEnd b) = _
  rw [← range_comp]
  exact cuspEnd_map_range b

theorem radialSlim_model_image (b : Bool) : slimPiece.map '' (slimModelFace b).val =
    {p | height p = if b then -(1 / 2 : ℝ) else -(1 / 4 : ℝ)} := by
  change slimToCarrier '' range (slimEnd b) = _
  rw [← range_comp]
  exact slimEnd_map_range b

theorem radialFaceIndex_image (f : Fin 4) : radialFaceSet f =
    (radialVertices.vertex (radialFaceIndex f).1).piece.map '' (radialFaceIndex f).2.val := by
  fin_cases f
  · exact (radialCusp_model_image false).symm
  · exact (radialCusp_model_image true).symm
  · exact (radialSlim_model_image false).symm
  · exact (radialSlim_model_image true).symm

end GC.GraphManifold.Assembly.FC39P0.X135Radial
