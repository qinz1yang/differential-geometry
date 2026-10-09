import DifferentialGeometry.Topology.LoopSpace.RadialExtension

noncomputable section

open Set Metric
open scoped NNReal

namespace DifferentialGeometry.Topology

def radialHomeomorph (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) : ℂ ≃ₜ ℂ where
  toFun := radialExtension κ
  invFun := radialExtension κ.symm
  left_inv z := by
    rw [← radialExtension_comp]
    have heq : (κ.symm ∘ κ : Circle → Circle) = id := funext κ.symm_apply_apply
    rw [heq, radialExtension_id]
  right_inv z := by
    rw [← radialExtension_comp]
    have heq : (κ ∘ κ.symm : Circle → Circle) = id := funext κ.apply_symm_apply
    rw [heq, radialExtension_id]
  continuous_toFun := (radialExtension_lipschitz hκ).continuous
  continuous_invFun := (radialExtension_lipschitz hκi).continuous

theorem radialHomeomorph_apply (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (z : ℂ) :
    radialHomeomorph κ hκ hκi z = radialExtension κ z := rfl

theorem radialHomeomorph_symm_apply (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (z : ℂ) :
    (radialHomeomorph κ hκ hκi).symm z = radialExtension κ.symm z := rfl

theorem radialHomeomorph_lipschitz (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) :
    LipschitzWith (2 * K + 1) (radialHomeomorph κ hκ hκi) :=
  radialExtension_lipschitz hκ

theorem radialHomeomorph_symm_lipschitz (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) :
    LipschitzWith (2 * L + 1) (radialHomeomorph κ hκ hκi).symm :=
  radialExtension_lipschitz hκi

theorem radialHomeomorph_norm (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (z : ℂ) :
    ‖radialHomeomorph κ hκ hκi z‖ = ‖z‖ := radialExtension_norm κ z

theorem radialHomeomorph_circle (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (z : Circle) :
    radialHomeomorph κ hκ hκi z = (κ z : ℂ) := radialExtension_circle κ z

theorem radialHomeomorph_image_closedBall (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (r : ℝ) :
    radialHomeomorph κ hκ hκi '' closedBall (0 : ℂ) r = closedBall (0 : ℂ) r := by
  let e := radialHomeomorph κ hκ hκi
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_closedBall, dist_zero_right, radialHomeomorph_norm] using hx
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    simpa only [mem_closedBall, dist_zero_right, e, radialHomeomorph_symm_apply,
      radialExtension_norm] using hz

theorem radialHomeomorph_image_ball (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (r : ℝ) :
    radialHomeomorph κ hκ hκi '' ball (0 : ℂ) r = ball (0 : ℂ) r := by
  let e := radialHomeomorph κ hκ hκi
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_ball, dist_zero_right, radialHomeomorph_norm] using hx
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    simpa only [mem_ball, dist_zero_right, e, radialHomeomorph_symm_apply,
      radialExtension_norm] using hz

theorem radialHomeomorph_image_sphere (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (r : ℝ) :
    radialHomeomorph κ hκ hκi '' sphere (0 : ℂ) r = sphere (0 : ℂ) r := by
  let e := radialHomeomorph κ hκ hκi
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_sphere, dist_zero_right, radialHomeomorph_norm] using hx
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    simpa only [mem_sphere, dist_zero_right, e, radialHomeomorph_symm_apply,
      radialExtension_norm] using hz

end DifferentialGeometry.Topology

end
