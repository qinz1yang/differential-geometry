import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonBase
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct
import DifferentialGeometry.Topology.Manifold.ProductSectionEmbedding
import DifferentialGeometry.Topology.Manifold.ImmersionCriterionInteriorTarget

/-!
The X136 closed slim singleton on the actual closed model S²×S¹. The second-factor map and the
sphere over Circle1 use the same product diffeomorphism and the actual empty model boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

def slimW : CompactCarrier.{0} := NoCuts.carrier sphereTwoTimesCircleLift

def slimPiece : PieceEmbedding slimW := wholePiece sphereTwoTimesCircleLift

def slimProduct : slimPiece.Piece ≃ₘ⟮𝓡∂ 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwo × Circle :=
  ((wholeDiffeomorph sphereTwoTimesCircleLift).trans
    sphereTwoTimesCircleModelCopy.equiv.symm).trans
      ((Diffeomorph.refl (𝓡 2) SphereTwo ∞).prodCongr sphereOneDiffeomorphCircle)

def slimProjection : slimPiece.Piece → Circle := Prod.snd ∘ slimProduct

theorem slimProjection_smooth : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ slimProjection :=
  contMDiff_snd.comp slimProduct.contMDiff

theorem slimProjection_submersion (x : slimPiece.Piece) :
    Surjective (mfderiv (𝓡∂ 3) (𝓡 1) slimProjection x) := by
  change Surjective (mfderiv (𝓡∂ 3) (𝓡 1) (Prod.snd ∘ slimProduct) x)
  rw [mfderiv_comp x mdifferentiableAt_snd
    (slimProduct.contMDiff.mdifferentiableAt (by simp)), mfderiv_snd]
  intro v
  obtain ⟨u, hu⟩ := (slimProduct.mfderivToContinuousLinearEquiv (by simp) x).surjective (0, v)
  refine ⟨u, ?_⟩
  change (slimProduct.mfderivToContinuousLinearEquiv (by simp) x u).2 = v
  rw [hu]

def slimSphereDown : ClosureSphere.{0} ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo :=
  (uliftDiffeomorph (𝓡 2) SphereTwo).symm

def slimSphereSection : SphereTwo → SphereTwo × Circle := fun z => (z, 1)

theorem slimSphereSection_embedding :
    IsSmoothEmbedding (𝓡 2) ((𝓡 2).prod (𝓡 1)) ∞ slimSphereSection :=
  isSmoothEmbedding_prodMk_const (1 : Circle)

def slimSphereMap : ClosureSphere.{0} → slimPiece.Piece :=
  slimProduct.symm ∘ slimSphereSection ∘ slimSphereDown

theorem slimSphereMap_smooth : ContMDiff (𝓡 2) (𝓡∂ 3) ∞ slimSphereMap :=
  slimProduct.symm.contMDiff.comp
    (slimSphereSection_embedding.contMDiff.comp slimSphereDown.contMDiff)

theorem slimSphereMap_derivative (z : ClosureSphere.{0}) :
    Injective (mfderiv (𝓡 2) (𝓡∂ 3) slimSphereMap z) := by
  rw [slimSphereMap, mfderiv_comp z
    (slimProduct.symm.contMDiff.mdifferentiableAt (by simp))
    ((slimSphereSection_embedding.contMDiff.comp slimSphereDown.contMDiff).mdifferentiableAt
      (by simp)), mfderiv_comp z (slimSphereSection_embedding.contMDiff.mdifferentiableAt
      (by simp)) (slimSphereDown.contMDiff.mdifferentiableAt (by simp))]
  intro v w hvw
  apply (slimSphereDown.mfderivToContinuousLinearEquiv (by simp) z).injective
  apply (slimSphereSection_embedding.isImmersion.isDiffImmersionAt (by simp)
    (slimSphereDown z)).injective
  apply (slimProduct.symm.mfderivToContinuousLinearEquiv (by simp)
    (slimSphereSection (slimSphereDown z))).injective
  exact hvw

theorem slimSphereMap_embedding : IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ slimSphereMap := by
  apply
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF
    (by simp) slimSphereMap_smooth
    (slimProduct.symm.toHomeomorph.isEmbedding.comp
      (slimSphereSection_embedding.isEmbedding.comp slimSphereDown.toHomeomorph.isEmbedding))
    slimSphereMap_derivative
  intro z
  apply (𝓡∂ 3).isInteriorPoint_iff_not_isBoundaryPoint (slimSphereMap z) |>.mpr
  intro hb
  have hempty : (𝓡∂ 3).boundary slimPiece.Piece = ∅ :=
    wholePiece_boundary sphereTwoTimesCircleLift
  have hb' : slimSphereMap z ∈ (𝓡∂ 3).boundary slimPiece.Piece := hb
  rw [hempty] at hb'
  exact hb'.elim

theorem slimSphereMap_range : range slimSphereMap = slimProjection ⁻¹' {1} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change (slimProduct (slimProduct.symm (slimSphereDown z, 1))).2 = 1
    rw [slimProduct.apply_symm_apply]
  · intro hx
    have hx' : (slimProduct x).2 = 1 := hx
    refine ⟨slimSphereDown.symm (slimProduct x).1, ?_⟩
    change slimProduct.symm (slimSphereDown (slimSphereDown.symm (slimProduct x).1), 1) = x
    rw [slimSphereDown.apply_symm_apply, ← hx']
    exact slimProduct.symm_apply_apply x

def slimFibre : SlimFibre slimPiece slimProjection :=
  .sphere slimSphereMap slimSphereMap_embedding slimSphereMap_range

def slimModel : SlimModel slimPiece :=
  .overCircle slimProjection slimProjection_smooth slimProjection_submersion slimFibre
    (wholePiece_boundary sphereTwoTimesCircleLift)

end GC.GraphManifold.Assembly.FC39P0.X136
