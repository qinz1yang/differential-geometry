import DifferentialGeometry.Geometry.Thurston.QuaternionPrismActions_X127_R17b
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismAxisSign_X127_R3b
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismHopfRotate_X127_R4b
import DifferentialGeometry.Geometry.Thurston.QuaternionAmbientHopf_X127
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Geometry GC.GraphManifold
open GC.Geometry.QuaternionPrismX127R3
open GC.Geometry.QuaternionPrismAxisSignX127
open GC.Geometry.QuaternionPrismHopfRotateX127
open GC.Geometry.QuaternionProjectiveX127
open GC.Geometry.QuaternionAmbientHopfX127
open scoped Manifold ContDiff

namespace GC.Geometry.QuaternionPrismHopfInvarianceX127

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "QH" => Quaternion ℝ
local notation "UQ" => unitary (Quaternion ℝ)

def rotateAmbient_X127 : E4 ≃ₗᵢ[ℝ] E4 := quaternionLeftHom rotateUnit_X127

def imaginaryVector_X127 (z : QH) : E3 := !₂[z.imI, -z.imJ, z.imK]

theorem imaginaryVector_neg_X127 (z : QH) :
    imaginaryVector_X127 (-z) = -imaginaryVector_X127 z := by
  ext i
  fin_cases i <;> simp [imaginaryVector_X127]

def axisBase_X127 (q : QH) : E3 :=
  imaginaryVector_X127 (star q * axisI_X127 * q)

def prismProjectedHopfCover_X127
    (x : Metric.sphere (0 : E4) 1) : RealProjectivePlane :=
  projectedHopf_X127
    (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127 x)

theorem axisBase_leftAction_X127 (g : UQ) (q : QH)
    (h : star (g : QH) * axisI_X127 * (g : QH) = axisI_X127 ∨
      star (g : QH) * axisI_X127 * (g : QH) = -axisI_X127) :
    axisBase_X127 ((g : QH) * q) = axisBase_X127 q ∨
      axisBase_X127 ((g : QH) * q) = -axisBase_X127 q := by
  rcases h with h | h
  · left
    unfold axisBase_X127
    exact congrArg imaginaryVector_X127 (calc
      star ((g : QH) * q) * axisI_X127 * ((g : QH) * q) =
          star q * (star (g : QH) * axisI_X127 * (g : QH)) * q := by
            rw [star_mul]
            noncomm_ring
      _ = star q * axisI_X127 * q := by rw [h])
  · right
    unfold axisBase_X127
    have hq : star ((g : QH) * q) * axisI_X127 * ((g : QH) * q) =
        -(star q * axisI_X127 * q) := by
      calc
        star ((g : QH) * q) * axisI_X127 * ((g : QH) * q) =
            star q * (star (g : QH) * axisI_X127 * (g : QH)) * q := by
              rw [star_mul]
              noncomm_ring
        _ = star q * (-axisI_X127) * q := by rw [h]
        _ = -(star q * axisI_X127 * q) := by noncomm_ring
    calc
      imaginaryVector_X127
          (star ((g : QH) * q) * axisI_X127 * ((g : QH) * q)) =
        imaginaryVector_X127 (-(star q * axisI_X127 * q)) :=
          congrArg imaginaryVector_X127 hq
      _ = -imaginaryVector_X127 (star q * axisI_X127 * q) :=
        imaginaryVector_neg_X127 _

theorem rotatedHopfVector_X127 (x : Metric.sphere (0 : E4) 1) :
    ((hopfMap (standardThreeSphereLiftDiffeomorph.{0}
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127 x)))).down :
      E3) = axisBase_X127 (s3Quat x) := by
  let y := DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127 x
  have hrot : s3Quat (y : E4) =
      (rotateUnit_X127 : QH) * s3Quat x := by
    change s3Quat (quaternionLeftHom rotateUnit_X127 (x : E4)) = _
    exact quaternionLeftHom_apply rotateUnit_X127 (x : E4)
  have hy : s3Quat (conjugateAmbient_X127 (y : E4)) =
      star ((rotateUnit_X127 : QH) * s3Quat x) := by
    rw [conjugateAmbient_quaternion_X127, hrot]
  have hpoint : conjugateAmbient_X127 (y : E4) =
      s3Quat.symm (star ((rotateUnit_X127 : QH) * s3Quat x)) := by
    apply s3Quat.injective
    rw [s3Quat.apply_symm_apply]
    exact hy
  calc
    _ = ambientHopf_X127 (conjugateAmbient_X127 (y : E4)) := hopfMap_lift_ambient_X127
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127 y)
    _ = quaternionHopfBase_X127
          (star ((rotateUnit_X127 : QH) * s3Quat x)) := by
      rw [hpoint]
      exact ambientHopf_s3Quat_X127 _
    _ = axisBase_X127 (s3Quat x) := by
      unfold quaternionHopfBase_X127 axisBase_X127
      exact congrArg imaginaryVector_X127 (calc
        star ((rotateUnit_X127 : QH) * s3Quat x) *
            quaternionEightHopfAxis_X127 *
            star (star ((rotateUnit_X127 : QH) * s3Quat x)) =
          star (s3Quat x) * (star (rotateUnit_X127 : QH) *
            quaternionEightHopfAxis_X127 * (rotateUnit_X127 : QH)) * s3Quat x := by
              simp only [star_mul, star_star]
              noncomm_ring
        _ = star (s3Quat x) * axisI_X127 * s3Quat x := by
          rw [rotate_axis_X127])

theorem prismProjectedHopfCover_invariant_X127 (n : ℕ) [NeZero n]
    (q : QuaternionGroup n) (x : Metric.sphere (0 : E4) 1) :
    prismProjectedHopfCover_X127
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
          (quaternionLeftHom (value_X127 n q)) x) =
      prismProjectedHopfCover_X127 x := by
  have haxis := value_normalizes_axisI_X127 n q
  have hbase := axisBase_leftAction_X127 (value_X127 n q) (s3Quat x) haxis
  have hact : s3Quat
      ((DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
        (quaternionLeftHom (value_X127 n q)) x : Metric.sphere (0 : E4) 1)) =
      (value_X127 n q : QH) * s3Quat x :=
    quaternionLeftHom_apply (value_X127 n q) (x : E4)
  change realProjectivePlaneQuotientMap
      (hopfMap (standardThreeSphereLiftDiffeomorph.{0}
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127
          (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127
            (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
              (quaternionLeftHom (value_X127 n q)) x))))).down =
    realProjectivePlaneQuotientMap
      (hopfMap (standardThreeSphereLiftDiffeomorph.{0}
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127
          (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127 x)))).down
  apply realProjectivePlaneQuotientMap_eq_iff.mpr
  rcases hbase with hbase | hbase
  · left
    apply Subtype.ext
    rw [rotatedHopfVector_X127, rotatedHopfVector_X127, hact]
    exact hbase
  · right
    rw [rotatedHopfVector_X127, rotatedHopfVector_X127, hact]
    exact hbase

end GC.Geometry.QuaternionPrismHopfInvarianceX127
