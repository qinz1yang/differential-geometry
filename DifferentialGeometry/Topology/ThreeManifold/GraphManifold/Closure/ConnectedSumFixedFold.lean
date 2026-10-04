import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ConnectedSumFold
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Opposite

/-!
The actual whole fold and its interior derivative identify the fixed oriented connected sum.
Changing the chosen oriented ball charts is discharged by the existing chart transport producer.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable (M N Q : ConnectedClosedOrientedManifold.{u} 3)
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (d : OrientedBallChart N.toClosedOrientedManifold)
  (fL : c.toBallChart.Punctured → Q.Carrier) (fR : d.toBallChart.Punctured → Q.Carrier)
  (hcross : ∀ x y, fL x = fR y ↔ ∃ z,
    c.toBallChart.boundaryMap z = x ∧
      d.toBallChart.boundaryMap (boundaryAttachment.1 z) = y)
  (hiL : Injective fL) (hiR : Injective fR)
  (hcover : ∀ y : Q.Carrier, (∃ x, fL x = y) ∨ ∃ x, fR x = y)
  (hsL : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fL ∘ c.toBallChart.interiorToPunctured))
  (hsR : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fR ∘ d.toBallChart.interiorToPunctured))
  (hsC : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (connectedSumFoldCollar M N Q c d boundaryAttachment fL fR))

def fixedConnectedSumChartDiffeomorph :
    (smoothConnectedSum M N c d boundaryAttachment).toConnectedClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum M N).Carrier :=
  (Classical.choice (nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    c (orientedBallChart M) d (orientedBallChart N) boundaryAttachment)).val

theorem fixedConnectedSumChartDiffeomorph_positive :
    (fixedConnectedSumChartDiffeomorph M N c d).preservesOrientation
      (smoothConnectedSum M N c d boundaryAttachment).orientation
      (connectedSum M N).orientation :=
  (Classical.choice (nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    c (orientedBallChart M) d (orientedBallChart N) boundaryAttachment)).property

def connectedSumFixedFoldDiffeomorph : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum M N).Carrier :=
  (connectedSumFoldDiffeomorph M N Q c d boundaryAttachment fL fR hcross
    hiL hiR hcover hsL hsR hsC).symm.trans (fixedConnectedSumChartDiffeomorph M N c d)

set_option backward.isDefEq.respectTransparency false in
theorem connectedSumFoldDiffeomorph_positive
    (x : c.toBallChart.interior)
    (hp : Orientation.map (Fin 3)
      ((hsL x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        (M.orientation.orientation x.val) =
          Q.orientation.orientation (fL (c.toBallChart.interiorToPunctured x))) :
    (connectedSumFoldDiffeomorph M N Q c d boundaryAttachment fL fR hcross
      hiL hiR hcover hsL hsR hsC).preservesOrientation
        (smoothConnectedSum M N c d boundaryAttachment).orientation Q.orientation := by
  let S := smoothConnectedSum M N c d boundaryAttachment
  let := S.charts
  let := S.smooth
  let F := connectedSumFoldDiffeomorph M N Q c d boundaryAttachment fL fR hcross
    hiL hiR hcover hsL hsR hsC
  let IL := ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart boundaryAttachment.1
  let A := (S.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) x).toLinearEquiv
  let B := (F.mfderivToContinuousLinearEquiv (by simp) (IL x)).toLinearEquiv
  let C := ((hsL x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  have hcomp : (F ∘ IL) = fL ∘ c.toBallChart.interiorToPunctured := by
    funext y
    rfl
  have hlin : A.trans B = C := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 3) (𝓡 3) F (IL x)
      (mfderiv (𝓡 3) (𝓡 3) IL x v) =
        mfderiv (𝓡 3) (𝓡 3) (fL ∘ c.toBallChart.interiorToPunctured) x v
    rw [← mfderiv_comp_apply x
      (F.contMDiff.mdifferentiableAt (by simp))
      (S.interiorLeft_localDiffeomorph.mdifferentiable (by simp) x)]
    exact congrArg (fun h => mfderiv (𝓡 3) (𝓡 3) h x v) hcomp
  have ha : Orientation.map (Fin 3) A (M.orientation.orientation x.val) =
      S.orientation.orientation (IL x) := S.interiorLeft_preserves_orientation x
  have hpoint : Orientation.map (Fin 3) B (S.orientation.orientation (IL x)) =
      Q.orientation.orientation (F (IL x)) := by
    rw [← ha, ← DifferentialGeometry.Topology.orientation_map_trans, hlin]
    exact hp
  exact Diffeomorph.preservesOrientation_of_eq_at F S.orientation Q.orientation (IL x) hpoint

set_option backward.isDefEq.respectTransparency false in
theorem connectedSumFixedFoldDiffeomorph_positive
    (x : c.toBallChart.interior)
    (hp : Orientation.map (Fin 3)
      ((hsL x).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        (M.orientation.orientation x.val) =
          Q.orientation.orientation (fL (c.toBallChart.interiorToPunctured x))) :
    (connectedSumFixedFoldDiffeomorph M N Q c d fL fR hcross hiL hiR hcover hsL hsR hsC
      ).preservesOrientation Q.orientation (connectedSum M N).orientation :=
  Diffeomorph.preservesOrientation_trans
    (Diffeomorph.preservesOrientation_symm
      (connectedSumFoldDiffeomorph_positive M N Q c d fL fR hcross hiL hiR hcover hsL hsR hsC
        x hp))
    (fixedConnectedSumChartDiffeomorph_positive M N c d)

include hcross hiL hiR hcover hsL hsR hsC in
theorem rawGraphPresentation_fixedConnectedSum_of_fold
    (G : RawGraphPresentation (GC.Endpoint.NoCuts.carrier Q)) :
    Nonempty (RawGraphPresentation (GC.Endpoint.NoCuts.carrier (connectedSum M N))) :=
  rawGraphPresentation_of_diffeomorph G
    (connectedSumFixedFoldDiffeomorph M N Q c d fL fR hcross hiL hiR hcover hsL hsR hsC)

end GC.GraphManifold
