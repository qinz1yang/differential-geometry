import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCompatibility
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapPatchCoordinates
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryAtlas

/-!
The genuine half-space smooth atlas on the compact quotient capping every spherical face.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

variable {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)

theorem exists_sphereCapQuotientAtlas :
    ∃ A : ChartedSpace (EuclideanHalfSpace 3) B.SphereCapQuotient, letI := A
      IsManifold (𝓡∂ 3) ∞ B.SphereCapQuotient ∧ ∀ a : B.SphereCapPatchIndex,
        ContMDiffOn (B.sphereCapPatchModel a) (𝓡∂ 3) ∞
          (B.sphereCapPatch a) (B.sphereCapPatch a).source ∧
        ContMDiffOn (𝓡∂ 3) (B.sphereCapPatchModel a) ∞
          (B.sphereCapPatch a).symm (B.sphereCapPatch a).target := by
  refine exists_carrierSurgeryAtlas_of_openCover (𝓡∂ 3) B.sphereCapPatch
    B.sphereCapPatch_cover B.sphereCapPatch_compatible ?_
  intro a x hx
  exact B.sphereCapPatch_coordinates a x

@[instance_reducible]
def sphereCapQuotientChartedSpace : ChartedSpace (EuclideanHalfSpace 3) B.SphereCapQuotient :=
  B.exists_sphereCapQuotientAtlas.choose

theorem sphereCapQuotientIsManifold :
    letI := B.sphereCapQuotientChartedSpace
    IsManifold (𝓡∂ 3) ∞ B.SphereCapQuotient :=
  B.exists_sphereCapQuotientAtlas.choose_spec.1

section Installed

variable [ChartedSpace (EuclideanHalfSpace 3) B.SphereCapQuotient]
  (hA : ∀ a : B.SphereCapPatchIndex,
    ContMDiffOn (B.sphereCapPatchModel a) (𝓡∂ 3) ∞
      (B.sphereCapPatch a) (B.sphereCapPatch a).source ∧
    ContMDiffOn (𝓡∂ 3) (B.sphereCapPatchModel a) ∞
      (B.sphereCapPatch a).symm (B.sphereCapPatch a).target)

def sphereCapPatchDiffeomorph (a : B.SphereCapPatchIndex) :
    PartialDiffeomorph (B.sphereCapPatchModel a) (𝓡∂ 3)
      (B.SphereCapPatchSpace a) B.SphereCapQuotient ∞ where
  __ := B.sphereCapPatch a
  contMDiffOn_toFun := (hA a).1
  contMDiffOn_invFun := (hA a).2

end Installed

end GC.GraphManifold.MixedBoundaryCertificate
