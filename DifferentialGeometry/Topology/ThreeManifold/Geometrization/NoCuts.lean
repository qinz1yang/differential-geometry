import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Statement
import DifferentialGeometry.Geometry.Thurston.Transport
import DifferentialGeometry.Topology.Manifold.ClosedOrientedPullback

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology
namespace GC.Endpoint
universe u

namespace NoCuts
variable (P : ConnectedClosedOrientedManifold.{u} 3)

abbrev carrier : CompactCarrier.{u} where
  kind := .closed
  Carrier := P.Carrier
  charts := inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 3)) P.Carrier)
  smooth := inferInstanceAs (IsManifold (𝓡 3) ∞ P.Carrier)
  secondCountable := ChartedSpace.secondCountable_of_sigmaCompact
    (EuclideanSpace ℝ (Fin 3)) P.Carrier
  orientation := P.orientation

private def openUnivDiffeomorph {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (U : TopologicalSpace.Opens M) (h : ∀ x : M, x ∈ U) : U ≃ₘ⟮𝓡 3, 𝓡 3⟯ M where
  toFun := Subtype.val
  invFun x := ⟨x, h x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U _).mp contMDiff_id

def interiorDiffeomorph : (carrier P).interior ≃ₘ⟮𝓡 3, 𝓡 3⟯ P.Carrier :=
  openUnivDiffeomorph _ (fun _ => BoundarylessManifold.isInteriorPoint)

def pieceInteriorDiffeomorph :
    (carrier P).pieceInterior ⊤ ≃ₘ⟮𝓡 3, 𝓡 3⟯ P.Carrier :=
  openUnivDiffeomorph _ (fun _ => ⟨trivial, BoundarylessManifold.isInteriorPoint⟩)

def components : (carrier P).Components where
  count := 1
  count_pos := by decide
  piece _ := ⊤
  closed _ := isClosed_univ
  connected _ := (openUnivDiffeomorph (⊤ : TopologicalSpace.Opens P.Carrier)
    (fun _ => trivial)).toHomeomorph.connectedSpace_iff.mpr inferInstance
  disjoint i j h := (h (Subsingleton.elim i j)).elim
  covers := by ext x; simp
  interior_connected _ := (pieceInteriorDiffeomorph P).toHomeomorph.connectedSpace_iff.mpr inferInstance

def boundary : TorusGluing (carrier P) where
  count := 0
  gluing := {
    left := fun i => i.elim0
    right := fun i => i.elim0
    attaching := fun i => i.elim0
    isClosed_left := fun i => i.elim0
    isClosed_right := fun i => i.elim0
    disjoint_left_right := fun i => i.elim0
    disjoint_blocks := fun i => i.elim0 }
  leftParam := fun i => i.elim0
  rightParam := fun i => i.elim0
  matching := fun i => i.elim0
  matching_eq := fun i => i.elim0
  torusOrientation := fun i => i.elim0
  leftCollar := fun i => i.elim0
  rightCollar := fun i => i.elim0
  left_source := fun i => i.elim0
  right_source := fun i => i.elim0
  left_zero := fun i => i.elim0
  right_zero := fun i => i.elim0
  boundary_exhausted := by
    change (𝓡 3).boundary P.Carrier = _
    rw [ModelWithCorners.Boundaryless.boundary_eq_empty]
    simp

def quotientHomeomorph : (boundary P).Assembled ≃ₜ P.Carrier :=
  (Homeomorph.Quotient.congrRight (fun x y => by
    change (x = y ∨ ∃ i : Fin 0, _) ↔ x = y
    simp)).trans Homeomorph.quotientBot

@[simp] theorem quotientHomeomorph_quotientMap (x : P.Carrier) :
    quotientHomeomorph P ((boundary P).quotientMap x) = x := rfl

def quotientManifold : ConnectedClosedOrientedManifold.{u} 3 :=
  P.pullback (quotientHomeomorph P)

def reconstruction : ClosedOrientedManifold.OrientedDiffeomorph
    (quotientManifold P).toClosedOrientedManifold P.toClosedOrientedManifold :=
  P.pullbackOrientedDiffeomorph (quotientHomeomorph P)

theorem quotientMap_eq_reconstruction_symm :
    ((boundary P).quotientMap : P.Carrier → (boundary P).Assembled) =
      (reconstruction P).val.symm := by
  funext x
  apply (quotientHomeomorph P).injective
  exact ((quotientHomeomorph P).apply_symm_apply x).symm

def assembly : SmoothAssembly (boundary P) := by
  let Q := quotientManifold P
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (boundary P).Assembled := Q.charts
  let : IsManifold (𝓡 3) ∞ (boundary P).Assembled := Q.smooth
  let d := reconstruction P
  let U : TopologicalSpace.Opens Q.Carrier := ⊤
  let e : U ≃ₘ⟮𝓡 3, 𝓡 3⟯ Q.Carrier := openUnivDiffeomorph U (fun _ => trivial)
  let di : (carrier P).interior ≃ₘ⟮𝓡 3, 𝓡 3⟯ U :=
    ((interiorDiffeomorph P).trans d.val.symm).trans e.symm
  refine {
    charts := Q.charts
    smooth := Q.smooth
    orientation := Q.orientation
    quotient_smooth := ?_
    quotient_oriented := ?_
    boundary_reversing := fun i => i.elim0
    interiorImage := U
    interiorDiffeomorph := di
    interior_map := ?_
    seam := fun i => i.elim0
    seam_source := fun i => i.elim0
    seam_zero := fun i => i.elim0
    seam_positive := fun i => i.elim0
    seam_negative := fun i => i.elim0 }
  · rw [quotientMap_eq_reconstruction_symm]
    exact d.val.symm.contMDiff
  · intro x
    rw [quotientMap_eq_reconstruction_symm]
    exact ⟨(d.val.symm.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv,
      fun _ => rfl, (d.symm.property x)⟩
  · intro x
    change d.val.symm x.val = (boundary P).quotientMap x.val
    rw [quotientMap_eq_reconstruction_symm]

def geometricDecomposition (G : GC.Geometry.GeometricStructure (𝓡 3) P.Carrier) :
    GeometricDecomposition P where
  carrier := carrier P
  components := components P
  boundary := boundary P
  assembly := assembly P
  reconstruction := reconstruction P
  incompressible := fun i => i.elim0
  leftPiece := fun i => i.elim0
  rightPiece := fun i => i.elim0
  left_owned := fun i => i.elim0
  right_owned := fun i => i.elim0
  geometry _ := by
    let : SigmaCompactSpace ((carrier P).pieceInterior ⊤) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3)
          ((carrier P).pieceInterior ⊤).isOpen)
    exact (carrier P).interiorGeometryOfOriginal ⊤
      (G.pullback (pieceInteriorDiffeomorph P) :
        GC.Geometry.GeometricStructure (𝓡 3) ((carrier P).pieceInterior ⊤))

end NoCuts
end GC.Endpoint
