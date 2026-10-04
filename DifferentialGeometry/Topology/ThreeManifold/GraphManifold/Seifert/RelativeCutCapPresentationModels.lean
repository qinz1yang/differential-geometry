import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationDefs
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometry

/-!
# Native compact pieces in a cut-cap assembly

A native piece has its actual compact carrier and the orientation pulled back from its canonical
map into the assembled cut carrier. The native-to-component diffeomorphism is positive. Explicit
surface products construct circle fibrations without assuming a Raw descendant presentation.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert
variable {W : CompactCarrier.{u}} {kind : CarrierModel}

def relativeCapNativePieceCarrier (S : EmbeddedCutSystem W kind) (i : Fin S.count) :
    CompactCarrier.{u} where
  kind := kind
  Carrier := S.Piece i
  charts := inferInstance
  smooth := inferInstance
  compact := inferInstance
  orientation := Manifold.manifoldOrientationPullback kind.model kind.model
    finrank_euclideanSpace_fin (S.pieceDiffeomorph i) (S.pieceDiffeomorph i).contMDiff
    (fun q => ((S.pieceDiffeomorph i).mfderivToContinuousLinearEquiv (by simp) q).bijective)
    (componentCarrier S.cutCarrier S.components i).orientation

def relativeCapNativePieceDiffeomorph (S : EmbeddedCutSystem W kind) (i : Fin S.count) :
    (relativeCapNativePieceCarrier S i).Carrier ≃ₘ⟮(relativeCapNativePieceCarrier S i).model,
      (componentCarrier S.cutCarrier S.components i).model⟯
      (componentCarrier S.cutCarrier S.components i).Carrier :=
  S.pieceDiffeomorph i

theorem relativeCapNativePieceDiffeomorph_positive (S : EmbeddedCutSystem W kind)
    (i : Fin S.count) : (relativeCapNativePieceDiffeomorph S i).preservesOrientation
      (relativeCapNativePieceCarrier S i).orientation
      (componentCarrier S.cutCarrier S.components i).orientation := by
  change (S.pieceDiffeomorph i).preservesOrientation
    (relativeCapNativePieceCarrier S i).orientation
    (componentCarrier S.cutCarrier S.components i).orientation
  intro q
  let f := S.pieceDiffeomorph i
  let hb : ∀ z, Bijective (mfderiv kind.model kind.model f z) :=
    fun z => (f.mfderivToContinuousLinearEquiv (by simp) z).bijective
  have he : (f.mfderivToContinuousLinearEquiv (by simp) q).toLinearEquiv =
      (Manifold.differentialEquivOfBijective kind.model kind.model f hb q).toLinearEquiv := by
    ext v
    rfl
  change Orientation.map (Fin 3)
    (f.mfderivToContinuousLinearEquiv (by simp) q).toLinearEquiv
    ((relativeCapNativePieceCarrier S i).orientation.orientation q) = _
  rw [he]
  exact Manifold.orientation_map_manifoldOrientationPullback kind.model kind.model
    finrank_euclideanSpace_fin f f.contMDiff hb
    (componentCarrier S.cutCarrier S.components i).orientation q

theorem relativeCapNativePieceDiffeomorph_apply (S : EmbeddedCutSystem W kind)
    (i : Fin S.count) (q : (relativeCapNativePieceCarrier S i).Carrier) :
    (relativeCapNativePieceDiffeomorph S i q).val = ⟨i, q⟩ := rfl

def relativeCapProductFibration (S : EmbeddedCutSystem W kind) (i : Fin S.count)
    (B : CompactSurface.{u})
    (e : (B.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.kind).prod (𝓡 1),
      (relativeCapNativePieceCarrier S i).model⟯ (relativeCapNativePieceCarrier S i).Carrier) :
    CircleFibration S.cutCarrier (S.components.piece i) :=
  CircleFibration.ofProductDiffeomorph B
    (e.trans (relativeCapNativePieceDiffeomorph S i)).symm

def relativeCapProductRaw (S : EmbeddedCutSystem W kind) (i : Fin S.count)
    (B : CompactSurface.{u})
    (e : (B.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.kind).prod (𝓡 1),
      (relativeCapNativePieceCarrier S i).model⟯ (relativeCapNativePieceCarrier S i).Carrier) :
    RawGraphPresentation (componentCarrier S.cutCarrier S.components i) :=
  (S.toTorusPresentation.ofPiece i).withFibration fun j =>
    Fin.cases ((relativeCapProductFibration S i B e).toComponent S.components i)
      (fun r => r.elim0) j

def relativeCapHyperbolicGeometry {C : CompactCarrier.{u}}
    (S : EmbeddedCutSystem W kind) (i : Fin S.count)
    (e : C.Carrier ≃ₘ⟮C.model, (relativeCapNativePieceCarrier S i).model⟯
      (relativeCapNativePieceCarrier S i).Carrier) (g : C.InteriorGeometry ⊤) :
    S.cutCarrier.InteriorGeometry (S.components.piece i) :=
  transportInteriorGeometry (pieceInteriorCongr
    ((topOpensDiffeomorph (I := C.model) C.Carrier).trans
      (e.trans (relativeCapNativePieceDiffeomorph S i)))).symm g

theorem relativeCapTransportInteriorGeometry_model {C D : CompactCarrier.{u}}
    {U : TopologicalSpace.Opens C.Carrier} {V : TopologicalSpace.Opens D.Carrier}
    (e : C.pieceInterior U ≃ₘ⟮C.model, D.model⟯ D.pieceInterior V)
    (g : D.InteriorGeometry V) :
    letI := Manifold.interiorChartedSpace C.model ∞ (M := C.pieceInterior U)
    letI := Manifold.interiorIsManifold C.model ∞ (M := C.pieceInterior U)
    letI := Manifold.interiorChartedSpace D.model ∞ (M := D.pieceInterior V)
    letI := Manifold.interiorIsManifold D.model ∞ (M := D.pieceInterior V)
    (transportInteriorGeometry e g).model = g.model := rfl

end GC.Seifert
