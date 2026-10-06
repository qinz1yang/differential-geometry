import DifferentialGeometry.Geometry.Thurston.QuaternionProjectiveHopf_X127
import DifferentialGeometry.Geometry.Thurston.QuaternionAmbientHopf_X127

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Geometry GC.GraphManifold
open GC.Geometry.QuaternionProjectiveX127
open GC.Geometry.QuaternionAmbientHopfX127
open scoped Manifold ContDiff

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace GC.Geometry.QuaternionHopfFibreX127

def ambientHopfToHopfS3Reflection_X127 (v : E3) : E3 := !₂[v 0, -v 1, v 2]

theorem ambientHopf_hopfS3_reflection_X127 (x : E4) :
    ambientHopf_X127 x = ambientHopfToHopfS3Reflection_X127 (hopfS3 x) := by
  have hbase : quaternionHopfBase_X127 (s3Quat x) =
      ambientHopfToHopfS3Reflection_X127 (hopfS3 x) := by
    rfl
  have h := ambientHopf_s3Quat_X127 (s3Quat x)
  have hx : s3Quat.symm (s3Quat x) = x := s3Quat.symm_apply_apply x
  rw [hx] at h
  exact h.trans hbase

theorem ambientHopfToHopfS3Reflection_injective_X127 :
    Function.Injective ambientHopfToHopfS3Reflection_X127 := by
  intro x y h
  have h0 := congrArg (fun z : E3 => z 0) h
  have h1 := congrArg (fun z : E3 => z 1) h
  have h2 := congrArg (fun z : E3 => z 2) h
  ext i
  fin_cases i
  · simpa [ambientHopfToHopfS3Reflection_X127] using h0
  · simpa [ambientHopfToHopfS3Reflection_X127] using h1
  · simpa [ambientHopfToHopfS3Reflection_X127] using h2

theorem quaternionEightHopfS3Action_X127 (q : QuaternionGroup 2) (x : E4) :
    hopfS3 ((quaternionEightSpaceFormEquiv q).val x) =
      quatRotate (quaternionEightHom q) (hopfS3 x) := by
  have hγ : (quaternionEightSpaceFormEquiv q).val =
      quaternionLeftHom (quaternionEightHom q) := rfl
  rw [hγ]
  change hopfS3 (s3Act (quaternionEightHom q, 1) x) = _
  exact hopfS3_s3Act (quaternionEightHom q, 1) x

theorem quaternionEightHopfFibresPreserved_X127 (q : QuaternionGroup 2)
    (x y : SphereCarrier.{0}) (hxy : hopfMap x = hopfMap y) :
    hopfMap (standardThreeSphereLiftDiffeomorph.{0}
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
        (quaternionEightSpaceFormEquiv q).val (sphereDownPoint x))) =
    hopfMap (standardThreeSphereLiftDiffeomorph.{0}
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
        (quaternionEightSpaceFormEquiv q).val (sphereDownPoint y))) := by
  have hdown := congrArg (fun v : SphereTwoLift.{0} => (v.down : E3)) hxy
  rw [hopfMap_ambient_X127 x, hopfMap_ambient_X127 y] at hdown
  have hS3 : hopfS3 (sphereDownPoint x) = hopfS3 (sphereDownPoint y) := by
    apply ambientHopfToHopfS3Reflection_injective_X127
    calc
      ambientHopfToHopfS3Reflection_X127 (hopfS3 (sphereDownPoint x)) =
          ambientHopf_X127 (sphereDownPoint x) :=
        (ambientHopf_hopfS3_reflection_X127 _).symm
      _ = ambientHopf_X127 (sphereDownPoint y) := hdown
      _ = ambientHopfToHopfS3Reflection_X127 (hopfS3 (sphereDownPoint y)) :=
        ambientHopf_hopfS3_reflection_X127 _
  have hactx := quaternionEightHopfS3Action_X127 q (sphereDownPoint x)
  have hacty := quaternionEightHopfS3Action_X127 q (sphereDownPoint y)
  have hAmbient :
      ambientHopf_X127 ((quaternionEightSpaceFormEquiv q).val (sphereDownPoint x)) =
        ambientHopf_X127 ((quaternionEightSpaceFormEquiv q).val (sphereDownPoint y)) := by
    calc
      ambientHopf_X127 ((quaternionEightSpaceFormEquiv q).val (sphereDownPoint x)) =
          ambientHopfToHopfS3Reflection_X127
            (quatRotate (quaternionEightHom q) (hopfS3 (sphereDownPoint x))) := by
              rw [ambientHopf_hopfS3_reflection_X127, hactx]
      _ = ambientHopfToHopfS3Reflection_X127
            (quatRotate (quaternionEightHom q) (hopfS3 (sphereDownPoint y))) :=
              congrArg (fun z => ambientHopfToHopfS3Reflection_X127
                (quatRotate (quaternionEightHom q) z)) hS3
      _ = ambientHopf_X127
            ((quaternionEightSpaceFormEquiv q).val (sphereDownPoint y)) := by
              rw [ambientHopf_hopfS3_reflection_X127, hacty]
  apply ULift.ext
  apply Subtype.ext
  rw [hopfMap_lift_ambient_X127, hopfMap_lift_ambient_X127]
  exact hAmbient

theorem quaternionEightSpaceForm_hopfFibrePreserving_X127 :
    ∀ (γ : quaternionEightSpaceForm.group) (x y : SphereCarrier.{0}),
      hopfMap x = hopfMap y →
      hopfMap (standardThreeSphereLiftDiffeomorph.{0}
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) γ.val (sphereDownPoint x))) =
      hopfMap (standardThreeSphereLiftDiffeomorph.{0}
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) γ.val (sphereDownPoint y))) := by
  intro γ x y hxy
  obtain ⟨q, hq⟩ := quaternionEightSpaceFormEquiv.surjective γ
  rw [← hq]
  exact quaternionEightHopfFibresPreserved_X127 q x y hxy

end GC.Geometry.QuaternionHopfFibreX127
