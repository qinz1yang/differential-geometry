import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialAdaptedRims
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial
local instance carrierCharts_SeamCoordinatesX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance
local instance carrierSmooth_SeamCoordinatesX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def radialNegativeForward (q : radialNegativeSeam) : radialCircleDomain :=
  ⟨negativeSeamToCarrier q, by
    change -1 < height (negativeSeamToCarrier q) ∧ height (negativeSeamToCarrier q) < 0
    rw [height_negativeSeam]
    exact q.property⟩

def radialNegativeInverse (p : radialCircleDomain) : radialNegativeSeam :=
  ⟨cliffordSeamInv p.val.val, p.property⟩

theorem radialNegative_sphere_target (p : radialCircleDomain) :
    p.val.val ∈ cliffordSeam.{0}.target :=
  ⟨(radialCircleToLoop p).property, sphereSecond_ne_zero_of_mem p.val.property⟩

theorem radialNegativeForward_smooth :
    ContMDiff signedCollarModel (𝓡∂ 3) ∞ radialNegativeForward := by
  apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    radialCircleDomain radialNegativeForward).mp
  exact negativeSeamToCarrier_smooth

theorem radialNegativeInverse_smooth :
    ContMDiff (𝓡∂ 3) signedCollarModel ∞ radialNegativeInverse := by
  apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
    radialNegativeSeam radialNegativeInverse).mp
  change ContMDiff (𝓡∂ 3) signedCollarModel ∞
    (fun p : radialCircleDomain => cliffordSeamInv p.val.val)
  have hs : ContMDiff (𝓡∂ 3) (𝓡 3) ∞
      (fun p : radialCircleDomain => p.val.val) :=
    contMDiff_solidTorus_val.comp contMDiff_subtype_val
  intro p
  have ht : ContMDiffAt (𝓡 3) signedCollarModel ∞ cliffordSeamInv p.val.val :=
    cliffordSeam.{0}.contMDiffOn_invFun.contMDiffAt
      (cliffordSeam.{0}.open_target.mem_nhds (radialNegative_sphere_target p))
  exact ht.comp p hs.contMDiffAt

def radialNegativeCoordinates : radialNegativeSeam
    ≃ₘ⟮signedCollarModel, 𝓡∂ 3⟯ radialCircleDomain where
  toFun := radialNegativeForward
  invFun := radialNegativeInverse
  left_inv q := by
    apply Subtype.ext
    change cliffordSeamInv (cliffordSeamMap q.val) = q.val
    exact cliffordSeam.{0}.left_inv ⟨q.property.1, q.property.2.trans (by norm_num)⟩
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change cliffordSeamMap (cliffordSeamInv p.val.val) = p.val.val
    exact cliffordSeam.{0}.right_inv (radialNegative_sphere_target p)
  contMDiff_toFun := radialNegativeForward_smooth
  contMDiff_invFun := radialNegativeInverse_smooth

def radialNegativePartial : PartialDiffeomorph signedCollarModel (𝓡∂ 3)
    (Torus × ℝ) carrier.Carrier ∞ :=
  ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph signedCollarModel
    radialNegativeSeam ⟨radialRimSeam (1 : Circle)⟩).symm.trans
      radialNegativeCoordinates.toPartialDiffeomorph).trans
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡∂ 3)
      radialCircleDomain ⟨radialRimPoint (1 : Circle)⟩)

theorem radialNegativePartial_apply (q : radialNegativeSeam) :
    radialNegativePartial q.val = negativeSeamToCarrier q := by
  change (radialNegativeCoordinates
    ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph signedCollarModel
      radialNegativeSeam ⟨radialRimSeam (1 : Circle)⟩).symm q.val)).val = _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply
    signedCollarModel radialNegativeSeam _ (x := q.val) q.property]
  rfl

theorem radialNegativePartial_source : radialNegativePartial.source =
    (radialNegativeSeam : Set (Torus × ℝ)) := by
  let A := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph signedCollarModel
    radialNegativeSeam ⟨radialRimSeam (1 : Circle)⟩
  change (A.symm.source ∩ A.symm ⁻¹' (univ : Set radialNegativeSeam)) ∩
    (fun x : Torus × ℝ => radialNegativeCoordinates (A.symm x)) ⁻¹'
      (univ : Set radialCircleDomain) = _
  simp only [preimage_univ, inter_univ]
  change A.target = _
  exact DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target
    signedCollarModel radialNegativeSeam _

end GC.GraphManifold.Assembly.FC39P0.X135Radial
