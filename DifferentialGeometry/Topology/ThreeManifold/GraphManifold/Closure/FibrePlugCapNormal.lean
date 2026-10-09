import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSolidModels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCapping

/-!
The actual cap normal partial diffeomorphism in the same canonical capping quotient.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold GC.Seifert GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

local instance boundedPlugCapBallCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance boundedPlugCapBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

def boundedPlugCapNormal (i : Fin B.sphereCount) :
    PartialDiffeomorph sphereSignedCollarModel B.sphereCapCarrier.model
      (ClosureSphere.{u} × ℝ) B.sphereCapCarrier.Carrier ∞ := by
  letI := B.sphereCapQuotientChartedSpace
  let hA := B.exists_sphereCapQuotientAtlas.choose_spec.2
  let R := (Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞).prodCongr
    boundedPlugCapProfileDiffeomorph
  exact R.toPartialDiffeomorph.trans (B.sphereCapPatchDiffeomorph hA (.inr (.inr i)))

theorem boundedPlugCapNormal_source (i : Fin B.sphereCount) :
    (B.boundedPlugCapNormal i).source =
      {p | (p.1, boundedPlugCapProfile p.2) ∈ sphereSignedCollarSource} := by
  change univ ∩ _ ⁻¹' (B.sphereCapSignedSeam i).source = _
  rw [univ_inter, B.sphereCapSignedSeam_source]
  rfl

theorem boundedPlugCapNormal_apply (i : Fin B.sphereCount)
    (z : ClosureSphere.{u}) (r : ℝ) :
    B.boundedPlugCapNormal i (z, r) =
      B.sphereCapSignedSeam i (z, boundedPlugCapProfile r) := rfl

theorem boundedPlugCapNormal_positive (i : Fin B.sphereCount)
    (z : ClosureSphere.{u}) {r : ℝ} (hr : 1 ≤ r) (hr1 : r ≤ 5 / 4) :
    B.boundedPlugCapNormal i (z, r) =
      B.sphereCapCore (B.sphere i (z, GC.Endpoint.halfPoint (2 * r - 2) (by linarith))) := by
  rw [B.boundedPlugCapNormal_apply, boundedPlugCapProfile_inner hr1]
  exact B.sphereCapSignedSeam_positive i z (2 * r - 2) (by linarith) (by linarith)

theorem boundedPlugCapNormal_negative (i : Fin B.sphereCount)
    (z : ClosureSphere.{u}) {r : ℝ} (hr : 3 / 4 < r) (hr1 : r ≤ 1) :
    B.boundedPlugCapNormal i (z, r) =
      B.sphereCapBall i (sphereCapBallCollar
        (z, GC.Endpoint.halfPoint (2 - 2 * r) (by linarith))) := by
  rw [B.boundedPlugCapNormal_apply, boundedPlugCapProfile_inner (by linarith)]
  have he : -(2 * r - 2) = 2 - 2 * r := by ring
  have hneg := B.sphereCapSignedSeam_negative i z (2 * r - 2)
    (by linarith) (by linarith)
  apply hneg.trans
  apply congrArg (B.sphereCapBall i)
  apply congrArg sphereCapBallCollar
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    ext k
    exact he

theorem boundedPlugCapNormal_actualCap (i : Fin B.sphereCount)
    (z : ClosureSphere.{u}) {r : ℝ} (hr : 3 / 4 < r) (hr1 : r ≤ 1) :
    B.boundedPlugCapNormal i (z, r) =
      B.sphereCapRelativeCapping.cap i
        ((B.sphereCapOrientationData.reparameterization i).symm
          (sphereCapBallCollar (z, GC.Endpoint.halfPoint (2 - 2 * r) (by linarith)))) := by
  rw [B.boundedPlugCapNormal_negative i z hr hr1]
  change B.sphereCapBall i _ = B.sphereCapBall i
    (B.sphereCapOrientationData.reparameterization i
      ((B.sphereCapOrientationData.reparameterization i).symm _))
  rw [Diffeomorph.apply_symm_apply]

theorem boundedPlugCapNormal_actualAttaching (i : Fin B.sphereCount)
    (z : ClosureSphere.{u}) :
    B.boundedPlugCapNormal i (z, 1) =
      B.sphereCapRelativeCapping.cap i
        (closureSphereToBall ((B.sphereCapOrientationData.attaching i).symm z)) := by
  rw [B.boundedPlugCapNormal_apply, boundedPlugCapProfile_inner (by norm_num)]
  norm_num only
  rw [B.sphereCapSignedSeam_zero]
  change B.sphereCapCore (B.sphere i (z, halfZero)) =
    B.sphereCapReparameterizedCap i _
  rw [B.sphereCapReparameterizedCap_boundary, Diffeomorph.apply_symm_apply]

end GC.GraphManifold.MixedBoundaryCertificate
