import DifferentialGeometry.Geometry.Metric.Radial
import Mathlib.Analysis.Normed.Module.Normalize

noncomputable section

open Set NormedSpace
open scoped InnerProductSpace ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ∞ω}

def radialBilinearField (a : ℝ → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  radialBilinearForm (NormedSpace.normalize x) ((a ‖x‖ / ‖x‖) ^ 2)

theorem radialBilinearField_apply (a : ℝ → ℝ) (x v w : E) :
    radialBilinearField a x v w =
      (a ‖x‖ / ‖x‖) ^ 2 * ⟪v, w⟫_ℝ +
        (1 - (a ‖x‖ / ‖x‖) ^ 2) * (⟪x, v⟫_ℝ / ‖x‖) * (⟪x, w⟫_ℝ / ‖x‖) := by
  simp only [radialBilinearField, radialBilinearForm_apply, NormedSpace.normalize, real_inner_smul_left]
  ring

theorem radialBilinearField_symm (a : ℝ → ℝ) (x v w : E) :
    radialBilinearField a x v w = radialBilinearField a x w v :=
  radialBilinearForm_symm _ _ _ _

@[simp] theorem radialBilinearField_zero (a : ℝ → ℝ) :
    radialBilinearField a (0 : E) = 0 := by
  ext v w
  simp [radialBilinearField_apply]

theorem contDiff_radialBilinearForm :
    ContDiff ℝ n (fun p : E × ℝ => radialBilinearForm p.1 p.2) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  let b : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  change ContDiff ℝ n (fun p : E × ℝ =>
    p.2 • b + (1 - p.2) • (b p.1).smulRight (b p.1))
  have hi : ContDiff ℝ n (fun p : E × ℝ => b p.1) :=
    b.contDiff.comp contDiff_fst
  exact (contDiff_snd.smul contDiff_const).add
    ((contDiff_const.sub contDiff_snd).smul (hi.smulRight hi))

theorem contDiffAt_radialBilinearField {a : ℝ → ℝ} {x : E}
    (ha : ContDiffAt ℝ n a ‖x‖) (hx : x ≠ 0) :
    ContDiffAt ℝ n (radialBilinearField a) x := by
  have hn : ContDiffAt ℝ n (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx
  have he : ContDiffAt ℝ n (NormedSpace.normalize : E → E) x :=
    (hn.inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
  have hc : ContDiffAt ℝ n (fun y : E => (a ‖y‖ / ‖y‖) ^ 2) x :=
    ((ha.comp x hn).div hn (norm_ne_zero_iff.mpr hx)).pow 2
  exact contDiff_radialBilinearForm.contDiffAt.comp x (he.prodMk hc)

theorem contDiffOn_radialBilinearField {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ n a (Ioi 0)) :
    ContDiffOn ℝ n (radialBilinearField a : E → E →L[ℝ] E →L[ℝ] ℝ) {x | x ≠ 0} := by
  intro x hx
  exact (contDiffAt_radialBilinearField
    (ha.contDiffAt (Ioi_mem_nhds (norm_pos_iff.mpr hx))) hx).contDiffWithinAt

theorem radialBilinearField_pos {a : ℝ → ℝ} {x v : E}
    (hx : x ≠ 0) (ha : a ‖x‖ ≠ 0) (hv : v ≠ 0) :
    0 < radialBilinearField a x v v :=
  radialBilinearForm_pos (norm_normalize hx)
    (sq_pos_of_ne_zero (div_ne_zero ha (norm_ne_zero_iff.mpr hx))) hv

theorem radialBilinearField_radial (a : ℝ → ℝ) (x v : E) :
    radialBilinearField a x x v = ⟪x, v⟫_ℝ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [radialBilinearField_apply, real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem radialBilinearField_radial_self (a : ℝ → ℝ) (x : E) :
    radialBilinearField a x x x = ‖x‖ ^ 2 := by
  rw [radialBilinearField_radial, real_inner_self_eq_norm_sq]

theorem radialBilinearField_unit_radial (a : ℝ → ℝ) {x : E}
    (hx : x ≠ 0) (v : E) :
    radialBilinearField a x (NormedSpace.normalize x) v = ⟪NormedSpace.normalize x, v⟫_ℝ :=
  radialBilinearForm_radial (norm_normalize hx) _ v

theorem radialBilinearField_unit_radial_self (a : ℝ → ℝ) {x : E} (hx : x ≠ 0) :
    radialBilinearField a x (NormedSpace.normalize x) (NormedSpace.normalize x) = 1 := by
  rw [radialBilinearField_unit_radial a hx, real_inner_self_eq_norm_sq, norm_normalize hx]
  norm_num

theorem radialBilinearField_tangential (a : ℝ → ℝ) (x w : E) {v : E}
    (hv : ⟪x, v⟫_ℝ = 0) :
    radialBilinearField a x v w = (a ‖x‖ / ‖x‖) ^ 2 * ⟪v, w⟫_ℝ := by
  simp only [radialBilinearField_apply, hv, zero_div, mul_zero, zero_mul, add_zero]

theorem radialBilinearField_lower_bound (a : ℝ → ℝ) {x : E} (hx : x ≠ 0) (v : E) :
    min ((a ‖x‖ / ‖x‖) ^ 2) 1 * ‖v‖ ^ 2 ≤ radialBilinearField a x v v :=
  radialBilinearForm_lower_bound (norm_normalize hx) _ v

theorem radialBilinearField_upper_bound (a : ℝ → ℝ) {x : E} (hx : x ≠ 0) (v : E) :
    radialBilinearField a x v v ≤ max ((a ‖x‖ / ‖x‖) ^ 2) 1 * ‖v‖ ^ 2 :=
  radialBilinearForm_upper_bound (norm_normalize hx) _ v

theorem inner_sq_le_radialBilinearField (a : ℝ → ℝ) {x : E} (hx : x ≠ 0) (v : E) :
    ⟪NormedSpace.normalize x, v⟫_ℝ ^ 2 ≤ radialBilinearField a x v v :=
  inner_sq_le_radialBilinearForm (norm_normalize hx) (sq_nonneg _) v

theorem radialBilinearField_linearIsometry
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E →ₗᵢ[ℝ] F) (a : ℝ → ℝ) (x v w : E) :
    radialBilinearField a (f x) (f v) (f w) = radialBilinearField a x v w := by
  simp only [radialBilinearField, NormedSpace.normalize, f.norm_map, ← f.map_smul]
  exact radialBilinearForm_linearIsometry f _ _ _ _

theorem radialBilinearField_polar (a : ℝ → ℝ) {e : E} (he : ‖e‖ = 1)
    {v w : E} (hv : ⟪e, v⟫_ℝ = 0) (hw : ⟪e, w⟫_ℝ = 0)
    {r : ℝ} (hr : 0 < r) (s t : ℝ) :
    radialBilinearField a (r • e) (s • e + r • v) (t • e + r • w) =
      s * t + a r ^ 2 * ⟪v, w⟫_ℝ := by
  have hnorm : ‖r • e‖ = r := by simp [norm_smul, abs_of_pos hr, he]
  rw [radialBilinearField, hnorm, normalize_smul_of_pos hr,
    normalize_eq_self_of_norm_eq_one he]
  exact radialBilinearForm_polar he hv hw hr.ne' (a r) s t

end DifferentialGeometry.Geometry.Riemannian
