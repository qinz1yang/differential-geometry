import DifferentialGeometry.Geometry.Thurston.QuaternionProjectiveHopf_X127
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Geometry GC.GraphManifold
open GC.Geometry.QuaternionProjectiveX127
open scoped Manifold ContDiff

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace GC.Geometry.QuaternionAmbientHopfX127

def quaternionHopfBase_X127 (z : Quaternion ℝ) : E3 :=
  !₂[(z * GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 *
      star z).imI,
    -(z * GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 *
      star z).imJ,
    (z * GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 *
      star z).imK]

theorem ambientHopf_s3Quat_X127 (z : Quaternion ℝ) :
    GC.Geometry.QuaternionProjectiveX127.ambientHopf_X127 (s3Quat.symm z) =
      quaternionHopfBase_X127 z := by
  change GC.Geometry.QuaternionProjectiveX127.ambientHopf_X127
      (!₂[z.re, -z.imK, z.imJ, -z.imI]) = quaternionHopfBase_X127 z
  ext i
  fin_cases i <;>
    simp [GC.Geometry.QuaternionProjectiveX127.ambientHopf_X127,
      quaternionHopfBase_X127,
      GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127] <;> ring

theorem quaternionHopfBase_right_normalizer_X127 (z r : Quaternion ℝ)
    (h : r * GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 * star r =
          GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 ∨
      r * GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 * star r =
          -GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127) :
    quaternionHopfBase_X127 (z * r) = quaternionHopfBase_X127 z ∨
      quaternionHopfBase_X127 (z * r) = -quaternionHopfBase_X127 z := by
  have hfactor :
      (z * r) * GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 *
          star (z * r) =
        z * (r * GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 *
          star r) * star z := by
    rw [star_mul]
    noncomm_ring
  rcases h with h | h
  · left
    unfold quaternionHopfBase_X127
    rw [hfactor, h]
  · right
    unfold quaternionHopfBase_X127
    rw [hfactor, h]
    ext i
    fin_cases i <;> simp

theorem quaternionEightAmbientHopf_invariant_or_neg_X127 (q : QuaternionGroup 2)
    (x : E4) :
    GC.Geometry.QuaternionProjectiveX127.ambientHopf_X127
        (GC.Geometry.QuaternionProjectiveX127.conjugateAmbient_X127
          ((quaternionEightSpaceFormEquiv q).val x)) =
        GC.Geometry.QuaternionProjectiveX127.ambientHopf_X127
          (GC.Geometry.QuaternionProjectiveX127.conjugateAmbient_X127 x) ∨
      GC.Geometry.QuaternionProjectiveX127.ambientHopf_X127
        (GC.Geometry.QuaternionProjectiveX127.conjugateAmbient_X127
          ((quaternionEightSpaceFormEquiv q).val x)) =
        -GC.Geometry.QuaternionProjectiveX127.ambientHopf_X127
          (GC.Geometry.QuaternionProjectiveX127.conjugateAmbient_X127 x) := by
  let qh : Quaternion ℝ := quaternionEightHom q
  let z : Quaternion ℝ := star (s3Quat x)
  let r : Quaternion ℝ := star qh
  have hγ : (quaternionEightSpaceFormEquiv q).val =
      quaternionLeftHom (quaternionEightHom q) := rfl
  have hconj :
      s3Quat (GC.Geometry.QuaternionProjectiveX127.conjugateAmbient_X127
        ((quaternionEightSpaceFormEquiv q).val x)) =
      star (s3Quat x) * star (quaternionEightHom q : Quaternion ℝ) := by
    rw [GC.Geometry.QuaternionProjectiveX127.conjugateAmbient_quaternion_X127,
      hγ, quaternionLeftHom_apply, star_mul]
  have hpoint :
      GC.Geometry.QuaternionProjectiveX127.conjugateAmbient_X127
          ((quaternionEightSpaceFormEquiv q).val x) =
        s3Quat.symm
          (star (s3Quat x) * star (quaternionEightHom q : Quaternion ℝ)) := by
    apply s3Quat.injective
    rw [s3Quat.apply_symm_apply]
    exact hconj
  have hx : GC.Geometry.QuaternionProjectiveX127.conjugateAmbient_X127 x =
      s3Quat.symm (star (s3Quat x)) := by
    apply s3Quat.injective
    rw [s3Quat.apply_symm_apply]
    exact GC.Geometry.QuaternionProjectiveX127.conjugateAmbient_quaternion_X127 x
  have haxis :=
    GC.Geometry.QuaternionProjectiveX127.quaternionEightHom_star_normalizes_hopf_axis_X127 q
  have hnorm :
      r * GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 * star r =
          GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 ∨
        r * GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 * star r =
          -GC.Geometry.QuaternionProjectiveX127.quaternionEightHopfAxis_X127 := by
    simpa [r, qh] using haxis
  rw [hpoint, hx, ambientHopf_s3Quat_X127, ambientHopf_s3Quat_X127]
  simpa [z, r, qh] using quaternionHopfBase_right_normalizer_X127 z r hnorm

theorem quaternionEightProjectedHopf_invariant_X127 (q : QuaternionGroup 2)
    (x : Metric.sphere (0 : E4) 1) :
    projectedHopf_X127
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
        (quaternionEightSpaceFormEquiv q).val x) = projectedHopf_X127 x := by
  have hpoly := quaternionEightAmbientHopf_invariant_or_neg_X127 q (x : E4)
  change realProjectivePlaneQuotientMap
      (hopfMap (standardThreeSphereLiftDiffeomorph.{0}
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127
          (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
            (quaternionEightSpaceFormEquiv q).val x)))).down =
    realProjectivePlaneQuotientMap
      (hopfMap (standardThreeSphereLiftDiffeomorph.{0}
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127 x))).down
  apply realProjectivePlaneQuotientMap_eq_iff.mpr
  rcases hpoly with h | h
  · left
    apply Subtype.ext
    rw [hopfMap_lift_ambient_X127, hopfMap_lift_ambient_X127]
    simpa only [DifferentialGeometry.Geometry.sphereDiffeo_coe] using h
  · right
    rw [hopfMap_lift_ambient_X127, hopfMap_lift_ambient_X127]
    simpa only [DifferentialGeometry.Geometry.sphereDiffeo_coe] using h

noncomputable def quaternionEightProjectedHopf_X127 :
    quaternionEightSpaceForm.Orbit → RealProjectivePlane :=
  Quotient.lift projectedHopf_X127 (by
    intro x y hxy
    have hprojection : quaternionEightSpaceForm.projection x =
        quaternionEightSpaceForm.projection y := Quotient.sound hxy
    obtain ⟨γ, hγ⟩ :=
      (quaternionEightSpaceForm.projection_eq_iff x y).mp hprojection
    obtain ⟨q, hq⟩ := quaternionEightSpaceFormEquiv.surjective γ
    rw [← hγ, ← hq]
    exact (quaternionEightProjectedHopf_invariant_X127 q x).symm)

theorem quaternionEightProjectedHopf_projection_X127
    (x : Metric.sphere (0 : E4) 1) :
    quaternionEightProjectedHopf_X127 (quaternionEightSpaceForm.projection x) =
      projectedHopf_X127 x := rfl

theorem quaternionEightProjectedHopf_smooth_X127 :
    ContMDiff (𝓡 3) (𝓡 2) ∞ quaternionEightProjectedHopf_X127 := by
  apply IsLocalDiffeomorph.contMDiff_of_comp_of_surjective
    quaternionEightSpaceForm.projection_isLocalDiffeomorph
    quaternionEightSpaceForm.projection_surjective
    ?_
  have hfactor :
      quaternionEightProjectedHopf_X127 ∘ quaternionEightSpaceForm.projection =
        projectedHopf_X127 := by
    funext x
    exact quaternionEightProjectedHopf_projection_X127 x
  rw [hfactor]
  exact projectedHopf_smooth_X127

theorem quaternionEightProjectedHopf_surjective_X127 :
    Function.Surjective quaternionEightProjectedHopf_X127 := by
  intro y
  obtain ⟨x, hx⟩ := projectedHopf_surjective_X127 y
  exact ⟨quaternionEightSpaceForm.projection x,
    (quaternionEightProjectedHopf_projection_X127 x).trans hx⟩

end GC.Geometry.QuaternionAmbientHopfX127
