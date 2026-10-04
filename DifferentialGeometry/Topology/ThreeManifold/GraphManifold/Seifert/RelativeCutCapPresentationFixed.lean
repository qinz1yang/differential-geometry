import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeSeifertNormalizationStage
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeCutCapPresentationData

/-!
# The prescribed mixed-stage presentation for a controlled cap

The torus parameters and width are supplied before the cap transition. Protected seams, surgery
support and frozen profiles remain distinct data. This file makes no choice of another frame or
width and does not convert a mixed stage to a global elementary presentation.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

def fixedCapPresentation (ψ : σ.toTorus.Side →
    (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    TorusPresentation (NoCuts.carrier Q) :=
  (σ.toTorus.reparam ψ).shrink hδ hδ1

def FixedCapData (ψ : σ.toTorus.Side →
    (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {P : ClosedOrientedManifold.{u} 3}
    (X : SphericalCutCapTransition Q.toClosedOrientedManifold P)
    (j : Fin σ.toTorus.pairing.count) (b : Bool) : Type _ :=
  ControlledCapPresentation (σ.fixedCapPresentation ψ hδ hδ1) X j σ.prot
    {σ.seamPiece j b, σ.hostPiece j b} σ.frozen σ.kind

end GC.Seifert.RelativeNormalization.MixedStage
