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

namespace GC.Geometry.QuaternionHopfBaseSignX127

def quaternionHopfAxisStabilizer_X127 : Set (QuaternionGroup 2) :=
  {q | star (quaternionEightHom q : Quaternion ℝ) * quaternionEightHopfAxis_X127 *
    (quaternionEightHom q : Quaternion ℝ) = quaternionEightHopfAxis_X127}

theorem quaternionEightHom_axisKernel_iff_X127 {q : QuaternionGroup 2} :
    q ∈ quaternionHopfAxisStabilizer_X127 ↔
      q = QuaternionGroup.a 0 ∨ q = QuaternionGroup.a 2 ∨
        q = QuaternionGroup.xa 1 ∨ q = QuaternionGroup.xa 3 := by
  rcases q with i | i
  · fin_cases i <;>
      norm_num [quaternionHopfAxisStabilizer_X127,
        quaternionEightHom_a_value_X127, quaternionEightHopfAxis_X127,
        QuaternionGroup.one_def, Quaternion.ext_iff] <;> decide
  · fin_cases i <;>
      norm_num [quaternionHopfAxisStabilizer_X127,
        quaternionEightHom_xa_value_X127, quaternionEightHopfAxis_X127,
        QuaternionGroup.one_def, Quaternion.ext_iff] <;> decide

theorem quaternionEightAmbientHopf_axisSign_X127 (q : QuaternionGroup 2) (x : E4) :
    (q ∈ quaternionHopfAxisStabilizer_X127 ∧
        ambientHopf_X127 (conjugateAmbient_X127 ((quaternionEightSpaceFormEquiv q).val x)) =
          ambientHopf_X127 (conjugateAmbient_X127 x)) ∨
      (q ∉ quaternionHopfAxisStabilizer_X127 ∧
        ambientHopf_X127 (conjugateAmbient_X127 ((quaternionEightSpaceFormEquiv q).val x)) =
          -ambientHopf_X127 (conjugateAmbient_X127 x)) := by
  classical
  by_cases hq : q ∈ quaternionHopfAxisStabilizer_X127
  · refine Or.inl ⟨hq, ?_⟩
    let qh : Quaternion ℝ := quaternionEightHom q
    let z : Quaternion ℝ := star (s3Quat x)
    let r : Quaternion ℝ := star qh
    have hγ : (quaternionEightSpaceFormEquiv q).val =
        quaternionLeftHom (quaternionEightHom q) := rfl
    have hconj :
        s3Quat (conjugateAmbient_X127 ((quaternionEightSpaceFormEquiv q).val x)) =
          star (s3Quat x) * star (quaternionEightHom q : Quaternion ℝ) := by
      rw [conjugateAmbient_quaternion_X127, hγ, quaternionLeftHom_apply, star_mul]
    have hpoint : conjugateAmbient_X127 ((quaternionEightSpaceFormEquiv q).val x) =
        s3Quat.symm (star (s3Quat x) * star (quaternionEightHom q : Quaternion ℝ)) := by
      apply s3Quat.injective
      rw [s3Quat.apply_symm_apply]
      exact hconj
    have hx : conjugateAmbient_X127 x = s3Quat.symm (star (s3Quat x)) := by
      apply s3Quat.injective
      rw [s3Quat.apply_symm_apply, conjugateAmbient_quaternion_X127]
    have hnorm :
        r * quaternionEightHopfAxis_X127 * star r = quaternionEightHopfAxis_X127 := by
      simpa [quaternionHopfAxisStabilizer_X127, r, qh] using hq
    have hfactor :
        (z * r) * quaternionEightHopfAxis_X127 * star (z * r) =
          z * (r * quaternionEightHopfAxis_X127 * star r) * star z := by
      rw [star_mul]
      noncomm_ring
    rw [hpoint, hx, ambientHopf_s3Quat_X127, ambientHopf_s3Quat_X127]
    change quaternionHopfBase_X127 (z * r) = quaternionHopfBase_X127 z
    unfold quaternionHopfBase_X127
    rw [hfactor, hnorm]
  · refine Or.inr ⟨hq, ?_⟩
    let qh : Quaternion ℝ := quaternionEightHom q
    let z : Quaternion ℝ := star (s3Quat x)
    let r : Quaternion ℝ := star qh
    have hγ : (quaternionEightSpaceFormEquiv q).val =
        quaternionLeftHom (quaternionEightHom q) := rfl
    have hconj :
        s3Quat (conjugateAmbient_X127 ((quaternionEightSpaceFormEquiv q).val x)) =
          star (s3Quat x) * star (quaternionEightHom q : Quaternion ℝ) := by
      rw [conjugateAmbient_quaternion_X127, hγ, quaternionLeftHom_apply, star_mul]
    have hpoint : conjugateAmbient_X127 ((quaternionEightSpaceFormEquiv q).val x) =
        s3Quat.symm (star (s3Quat x) * star (quaternionEightHom q : Quaternion ℝ)) := by
      apply s3Quat.injective
      rw [s3Quat.apply_symm_apply]
      exact hconj
    have hx : conjugateAmbient_X127 x = s3Quat.symm (star (s3Quat x)) := by
      apply s3Quat.injective
      rw [s3Quat.apply_symm_apply, conjugateAmbient_quaternion_X127]
    have haxis := quaternionEightHom_star_normalizes_hopf_axis_X127 q
    have hnot :
        star (quaternionEightHom q : Quaternion ℝ) * quaternionEightHopfAxis_X127 *
            (quaternionEightHom q : Quaternion ℝ) ≠ quaternionEightHopfAxis_X127 := by
      intro h
      exact hq (by simpa [quaternionHopfAxisStabilizer_X127] using h)
    have hnorm :
        r * quaternionEightHopfAxis_X127 * star r = -quaternionEightHopfAxis_X127 := by
      rcases haxis with hplus | hminus
      · exact (hnot (by simpa [r, qh] using hplus)).elim
      · simpa [r, qh] using hminus
    have hfactor :
        (z * r) * quaternionEightHopfAxis_X127 * star (z * r) =
          z * (r * quaternionEightHopfAxis_X127 * star r) * star z := by
      rw [star_mul]
      noncomm_ring
    rw [hpoint, hx, ambientHopf_s3Quat_X127, ambientHopf_s3Quat_X127]
    change quaternionHopfBase_X127 (z * r) = -quaternionHopfBase_X127 z
    unfold quaternionHopfBase_X127
    rw [hfactor, hnorm]
    ext i
    fin_cases i <;> simp

end GC.Geometry.QuaternionHopfBaseSignX127
