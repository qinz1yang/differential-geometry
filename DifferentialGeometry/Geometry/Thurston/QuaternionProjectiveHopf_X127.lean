import DifferentialGeometry.Geometry.Thurston.QuaternionSphereActions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.HopfSphere
import DifferentialGeometry.Topology.ProjectiveSpace.Manifold

/-!
Actual quaternion conjugation and its Hopf projection into the real projective plane.
These maps support reconstruction of the quaternion quotient circle bundle; no quotient
fibration or Raw presentation is asserted by these definitions.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open scoped Manifold ContDiff

attribute [local instance] uliftChartedSpace isManifold_ulift

namespace GC.Geometry.QuaternionProjectiveX127

local notation "E4" => EuclideanSpace ℝ (Fin 4)

def conjugateQuaternion_X127 : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := star_add
  map_smul' := Quaternion.star_smul
  norm_map' := Quaternion.norm_star

def conjugateAmbient_X127 : E4 ≃ₗᵢ[ℝ] E4 :=
  (s3Quat.trans conjugateQuaternion_X127).trans s3Quat.symm

def projectedHopf_X127 (x : Metric.sphere (0 : E4) 1) : RealProjectivePlane :=
  realProjectivePlaneQuotientMap (hopfMap (standardThreeSphereLiftDiffeomorph.{0}
    (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127 x))).down


local instance instFinrankThree_X127 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem conjugateAmbient_quaternion_X127 (x : E4) :
    s3Quat (conjugateAmbient_X127 x) = star (s3Quat x) := by
  change s3Quat (s3Quat.symm (star (s3Quat x))) = star (s3Quat x)
  exact s3Quat.apply_symm_apply _

theorem projectedHopf_smooth_X127 :
    ContMDiff (𝓡 3) (𝓡 2) ∞ projectedHopf_X127 := by
  let d := (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127).trans
    standardThreeSphereLiftDiffeomorph.{0}
  have hHopf : ContMDiff (𝓡 3) (𝓡 2) ∞
      (fun x => (hopfMap (d x)).down) :=
    (uliftDiffeomorph.{0, 0} (𝓡 2) (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 3)) 1)).symm.contMDiff.comp
        (contMDiff_hopfMap.comp d.contMDiff)
  exact realProjectiveSpaceQuotientMap_isLocalDiffeomorph.contMDiff.comp hHopf

theorem projectedHopf_surjective_X127 : Function.Surjective projectedHopf_X127 := by
  let d := (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127).trans
    standardThreeSphereLiftDiffeomorph.{0}
  intro b
  obtain ⟨y, hy⟩ := realProjectivePlaneQuotientMap_surjective b
  obtain ⟨z, hz⟩ := hopfMap_surjective.{0} (ULift.up y)
  refine ⟨d.symm z, ?_⟩
  change realProjectivePlaneQuotientMap (hopfMap (d (d.symm z))).down = b
  rw [d.apply_symm_apply, hz]
  exact hy

def ambientHopf_X127 (x : E4) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * (x 0 * x 2 + x 1 * x 3), 2 * (x 1 * x 2 - x 0 * x 3),
    x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2]

theorem conjugateAmbient_apply_X127 (x : E4) :
    conjugateAmbient_X127 x = !₂[x 0, -x 1, -x 2, -x 3] := by
  apply s3Quat.injective
  rw [conjugateAmbient_quaternion_X127]
  ext <;> simp [s3Quat]

theorem hopfMap_ambient_X127 (p : SphereCarrier.{0}) :
    ((hopfMap p).down : EuclideanSpace ℝ (Fin 3)) = ambientHopf_X127 (sphereDown p) := by
  change planeHeightCoordinates.symm (hopfPlane p, cliffordHeight p) =
    ambientHopf_X127 (sphereDown p)
  ext i
  fin_cases i <;>
    simp [planeHeightCoordinates, hopfPlane, cliffordHeight, sphereFirst, sphereSecond,
      pairCoordinates, ambientHopf_X127, Complex.sq_norm, Complex.normSq_apply] <;> ring

theorem hopfMap_lift_ambient_X127 (x : Metric.sphere (0 : E4) 1) :
    ((hopfMap (standardThreeSphereLiftDiffeomorph.{0} x)).down :
      EuclideanSpace ℝ (Fin 3)) = ambientHopf_X127 (x : E4) := by
  have hdown : sphereDown (standardThreeSphereLiftDiffeomorph.{0} x) = (x : E4) :=
    congrArg (fun z : Metric.sphere (0 : E4) 1 => (z : E4))
      (standardThreeSphereLiftDiffeomorph.{0}.symm_apply_apply x)
  exact (hopfMap_ambient_X127 _).trans (congrArg ambientHopf_X127 hdown)

def quaternionEightHopfAxis_X127 : Quaternion ℝ := ⟨0, 0, 0, 1⟩

theorem quaternionEightHom_a_value_X127 (i : Fin 4) :
    (quaternionEightHom (QuaternionGroup.a i) : Quaternion ℝ) =
      ![(1 : Quaternion ℝ), ⟨0, 1, 0, 0⟩, -1, ⟨0, -1, 0, 0⟩] i := by
  fin_cases i <;> rfl

theorem quaternionEightHom_xa_value_X127 (i : Fin 4) :
    (quaternionEightHom (QuaternionGroup.xa i) : Quaternion ℝ) =
      ![⟨0, 0, 1, 0⟩, ⟨0, 0, 0, -1⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 0, 1⟩] i := by
  fin_cases i <;> rfl

theorem quaternionEightHom_star_normalizes_hopf_axis_X127
    (q : QuaternionGroup 2) :
    star (quaternionEightHom q : Quaternion ℝ) * quaternionEightHopfAxis_X127 *
        (quaternionEightHom q : Quaternion ℝ) = quaternionEightHopfAxis_X127 ∨
      star (quaternionEightHom q : Quaternion ℝ) * quaternionEightHopfAxis_X127 *
        (quaternionEightHom q : Quaternion ℝ) = -quaternionEightHopfAxis_X127 := by
  rcases q with i | i
  · fin_cases i
    · left
      apply Quaternion.ext <;> norm_num [quaternionEightHopfAxis_X127,
        quaternionEightHom_a_value_X127]
    · right
      apply Quaternion.ext <;> norm_num [quaternionEightHopfAxis_X127,
        quaternionEightHom_a_value_X127]
    · left
      apply Quaternion.ext <;> norm_num [quaternionEightHopfAxis_X127,
        quaternionEightHom_a_value_X127]
    · right
      apply Quaternion.ext <;> norm_num [quaternionEightHopfAxis_X127,
        quaternionEightHom_a_value_X127]
  · fin_cases i
    · right
      apply Quaternion.ext <;> norm_num [quaternionEightHopfAxis_X127,
        quaternionEightHom_xa_value_X127]
    · left
      apply Quaternion.ext <;> norm_num [quaternionEightHopfAxis_X127,
        quaternionEightHom_xa_value_X127]
    · right
      apply Quaternion.ext <;> norm_num [quaternionEightHopfAxis_X127,
        quaternionEightHom_xa_value_X127]
    · left
      apply Quaternion.ext <;> norm_num [quaternionEightHopfAxis_X127,
        quaternionEightHom_xa_value_X127]

end GC.Geometry.QuaternionProjectiveX127
