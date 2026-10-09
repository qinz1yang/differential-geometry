import DifferentialGeometry.Analysis.Calculus.Interpolation.RadialCone
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal Topology

namespace DifferentialGeometry.Topology

/-- Change radius along each unit direction; the choice of direction at zero is harmless. -/
def radialProfile (R : loopCircle → ℝ) (z : ℂ) : ℂ :=
  R (polarAnnulusCoordinates z).2 • z

/-- The reciprocal radial change on the same directions. -/
def radialProfileInv (R : loopCircle → ℝ) (z : ℂ) : ℂ :=
  radialProfile (fun θ => (R θ)⁻¹) z

@[simp] theorem radialProfile_zero (R : loopCircle → ℝ) : radialProfile R 0 = 0 := by
  simp only [radialProfile, smul_zero]

@[simp] theorem radialProfileInv_zero (R : loopCircle → ℝ) : radialProfileInv R 0 = 0 :=
  radialProfile_zero _

theorem radialProfile_direction {R : loopCircle → ℝ} (hR : ∀ θ, 0 < R θ) (z : ℂ) :
    radialDirection (radialProfile R z) = radialDirection z := by
  by_cases hz : z = 0
  · simp only [hz, radialProfile_zero]
  · have heq : radialProfile R z =
        (R (polarAnnulusCoordinates z).2 * ‖z‖) • (radialDirection z : ℂ) := by
      rw [mul_smul, radialDirection_reconstruct]
      rfl
    rw [heq, radialDirection_pos_smul (mul_pos (hR _) (norm_pos_iff.mpr hz))]

theorem radialProfile_parameter {R : loopCircle → ℝ} (hR : ∀ θ, 0 < R θ) (z : ℂ) :
    (polarAnnulusCoordinates (radialProfile R z)).2 = (polarAnnulusCoordinates z).2 := by
  simp only [polarAnnulusCoordinates, radialProfile_direction hR]

theorem radialProfileInv_parameter {R : loopCircle → ℝ} (hR : ∀ θ, 0 < R θ) (z : ℂ) :
    (polarAnnulusCoordinates (radialProfileInv R z)).2 = (polarAnnulusCoordinates z).2 :=
  radialProfile_parameter (fun θ => inv_pos.mpr (hR θ)) z

theorem radialProfileInv_radialProfile {R : loopCircle → ℝ}
    (hR : ∀ θ, 0 < R θ) (z : ℂ) : radialProfileInv R (radialProfile R z) = z := by
  change (R (polarAnnulusCoordinates (radialProfile R z)).2)⁻¹ • radialProfile R z = z
  rw [radialProfile_parameter hR]
  simp only [radialProfile, smul_smul, inv_mul_cancel₀ (hR _).ne', one_smul]

theorem radialProfile_radialProfileInv {R : loopCircle → ℝ}
    (hR : ∀ θ, 0 < R θ) (z : ℂ) : radialProfile R (radialProfileInv R z) = z := by
  change R (polarAnnulusCoordinates (radialProfileInv R z)).2 • radialProfileInv R z = z
  rw [radialProfileInv_parameter hR]
  simp only [radialProfileInv, radialProfile, smul_smul, mul_inv_cancel₀ (hR _).ne', one_smul]

theorem norm_radialProfile {R : loopCircle → ℝ} (hR : ∀ θ, 0 < R θ) (z : ℂ) :
    ‖radialProfile R z‖ = R (polarAnnulusCoordinates z).2 * ‖z‖ := by
  simp only [radialProfile, norm_smul, Real.norm_eq_abs, abs_of_pos (hR _)]

theorem norm_radialProfileInv {R : loopCircle → ℝ} (hR : ∀ θ, 0 < R θ) (z : ℂ) :
    ‖radialProfileInv R z‖ = ‖z‖ / R (polarAnnulusCoordinates z).2 := by
  rw [radialProfileInv, norm_radialProfile (fun θ => inv_pos.mpr (hR θ))]
  exact (div_eq_inv_mul _ _).symm

theorem radialProfile_image_closedBall {R : loopCircle → ℝ} (hR : ∀ θ, 0 < R θ) :
    radialProfile R '' closedBall (0 : ℂ) 1 =
      {z : ℂ | ‖z‖ ≤ R (polarAnnulusCoordinates z).2} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ‖radialProfile R x‖ ≤ R (polarAnnulusCoordinates (radialProfile R x)).2
    rw [norm_radialProfile hR, radialProfile_parameter hR]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) (hR _).le).trans_eq
      (mul_one _)
  · intro hz
    refine ⟨radialProfileInv R z, ?_, radialProfile_radialProfileInv hR z⟩
    rw [mem_closedBall_zero_iff, norm_radialProfileInv hR]
    exact (div_le_one (hR _)).mpr hz

theorem radialProfile_eq_self {R : loopCircle → ℝ} {z : ℂ}
    (hR : R (polarAnnulusCoordinates z).2 = 1) : radialProfile R z = z := by
  simp only [radialProfile, hR, one_smul]

theorem radialProfileInv_eq_self {R : loopCircle → ℝ} {z : ℂ}
    (hR : R (polarAnnulusCoordinates z).2 = 1) : radialProfileInv R z = z := by
  simp only [radialProfileInv, radialProfile, hR, inv_one, one_smul]

private theorem circle_radius_lipschitz {R : loopCircle → ℝ} {K B : ℝ≥0}
    (hR : LipschitzWith K R) (hB : ∀ θ, ‖R θ‖ ≤ B) :
    LipschitzWith (K + B) (fun c : Circle =>
      R ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm c) • (c : ℂ)) := by
  let e := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
  have hf : LipschitzWith K (R ∘ e) := by
    simpa only [mul_one] using hR.comp circle_parameter_lipschitz
  apply LipschitzWith.of_dist_le_mul
  intro c d
  change dist (R (e c) • (c : ℂ)) (R (e d) • (d : ℂ)) ≤ ((K : ℝ) + B) * dist c d
  have hsplit : R (e c) • (c : ℂ) - R (e d) • (d : ℂ) =
      R (e c) • ((c : ℂ) - (d : ℂ)) + (R (e c) - R (e d)) • (d : ℂ) := by
    simp only [smul_sub, sub_smul]
    abel
  rw [dist_eq_norm, hsplit]
  calc
    _ ≤ ‖R (e c) • ((c : ℂ) - (d : ℂ))‖ +
        ‖(R (e c) - R (e d)) • (d : ℂ)‖ := norm_add_le _ _
    _ = ‖R (e c)‖ * dist c d + dist (R (e c)) (R (e d)) := by
      rw [norm_smul, norm_smul, Circle.norm_coe, mul_one]
      have hd : dist c d = ‖(c : ℂ) - (d : ℂ)‖ := Complex.dist_eq _ _
      rw [hd, dist_eq_norm]
    _ ≤ (B : ℝ) * dist c d + K * dist c d :=
      add_le_add (mul_le_mul_of_nonneg_right (hB _) dist_nonneg) (hf.dist_le_mul c d)
    _ = _ := by ring

private theorem reciprocal_radius_lipschitz {R : loopCircle → ℝ} {K : ℝ≥0}
    (hR : LipschitzWith K R) (hlo : ∀ θ, 1 / 2 ≤ R θ) :
    LipschitzWith (4 * K) (fun θ => (R θ)⁻¹) := by
  have hpos (θ : loopCircle) : 0 < R θ := lt_of_lt_of_le (by norm_num) (hlo θ)
  have hinv (θ : loopCircle) : (R θ)⁻¹ ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hlo θ)
    norm_num only [one_div, inv_div, inv_one, div_one] at h
    exact h
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, inv_sub_inv' (hpos x).ne' (hpos y).ne', abs_mul, abs_mul,
    abs_of_pos (inv_pos.mpr (hpos x)), abs_of_pos (inv_pos.mpr (hpos y))]
  have hdiff : |R y - R x| ≤ (K : ℝ) * dist x y := by
    simpa only [Real.dist_eq, abs_sub_comm] using hR.dist_le_mul x y
  calc
    _ ≤ 2 * |R y - R x| * 2 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right (hinv x) (abs_nonneg _)) (hinv y)
        (inv_pos.mpr (hpos y)).le (by positivity)
    _ ≤ ((4 * K : ℝ≥0) : ℝ) * dist x y := by
      change _ ≤ (4 * (K : ℝ)) * dist x y
      linarith


private theorem radialProfile_lipschitz_of_bound {R : loopCircle → ℝ} {K B : ℝ≥0}
    (hR : LipschitzWith K R) (hB : ∀ θ, ‖R θ‖ ≤ B) :
    LipschitzWith (2 * (K + B) + B) (radialProfile R) := by
  let b : Circle → ℂ := fun c =>
    R ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm c) • (c : ℂ)
  have hb : LipschitzWith (K + B) b := circle_radius_lipschitz hR hB
  have hbound (c : Circle) : ‖b c - 0‖ ≤ B := by
    simp only [b, sub_zero, norm_smul, Circle.norm_coe, mul_one]
    exact hB _
  have hcone := radialCone_lipschitz hb hbound
  have heq : radialCone (0 : ℂ) b = radialProfile R := by
    funext z
    simp only [radialCone, sub_zero, zero_add, b, radialProfile, polarAnnulusCoordinates]
    rw [smul_comm, radialDirection_reconstruct]
  rwa [heq] at hcone

/-- A bounded Lipschitz radius profile gives a global Lipschitz radial change, including zero. -/
theorem radialProfile_lipschitz {R : loopCircle → ℝ} {K : ℝ≥0}
    (hR : LipschitzWith K R) (hlo : ∀ θ, 1 / 2 ≤ R θ) (hhi : ∀ θ, R θ ≤ 1) :
    LipschitzWith (2 * K + 3) (radialProfile R) := by
  have hb (θ : loopCircle) : ‖R θ‖ ≤ (1 : ℝ≥0) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) (hlo θ))]
    exact hhi θ
  convert radialProfile_lipschitz_of_bound hR hb using 1; ring

/-- The reciprocal radial map is globally Lipschitz under the same positive lower bound. -/
theorem radialProfileInv_lipschitz {R : loopCircle → ℝ} {K : ℝ≥0}
    (hR : LipschitzWith K R) (hlo : ∀ θ, 1 / 2 ≤ R θ) :
    LipschitzWith (8 * K + 6) (radialProfileInv R) := by
  have hb (θ : loopCircle) : ‖(R θ)⁻¹‖ ≤ (2 : ℝ≥0) := by
    have hpos : 0 < R θ := lt_of_lt_of_le (by norm_num) (hlo θ)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hlo θ)
    norm_num only [one_div, inv_div, inv_one, div_one] at h
    exact h
  change LipschitzWith (8 * K + 6) (radialProfile (fun θ => (R θ)⁻¹))
  convert radialProfile_lipschitz_of_bound (reciprocal_radius_lipschitz hR hlo) hb using 1;
    ring

/-- The inner star disk is closed and therefore measurable; no differentiability at zero is used. -/
theorem isClosed_radialProfile_star {R : loopCircle → ℝ} {K : ℝ≥0}
    (hR : LipschitzWith K R) (hlo : ∀ θ, 1 / 2 ≤ R θ) :
    IsClosed {z : ℂ | ‖z‖ ≤ R (polarAnnulusCoordinates z).2} := by
  have hpos (θ : loopCircle) : 0 < R θ := lt_of_lt_of_le (by norm_num) (hlo θ)
  have heq : {z : ℂ | ‖z‖ ≤ R (polarAnnulusCoordinates z).2} =
      radialProfileInv R ⁻¹' closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff,
      norm_radialProfileInv hpos]
    exact (div_le_one (hpos _)).symm
  rw [heq]
  exact isClosed_closedBall.preimage (radialProfileInv_lipschitz hR hlo).continuous

end DifferentialGeometry.Topology
