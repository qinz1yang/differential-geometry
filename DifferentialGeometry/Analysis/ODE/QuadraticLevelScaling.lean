import DifferentialGeometry.Analysis.ODE.QuadraticRadialCurve
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

open Set
open scoped ContDiff Pointwise

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def quadraticLevelScaling (a c : ℝ) (x : E) (t : ℝ) : E :=
  Real.sqrt ((t - c) / (a - c)) • x

noncomputable def quadraticLevelVectorField (c : ℝ) (p : ℝ × E) : E :=
  (2 * (p.1 - c))⁻¹ • p.2

@[simp]
theorem quadraticLevelScaling_self {a c : ℝ} (hac : a ≠ c) (x : E) :
    quadraticLevelScaling a c x a = x := by
  simp [quadraticLevelScaling, sub_ne_zero.mpr hac]

theorem norm_sq_quadraticLevelScaling (a c : ℝ) (x : E) {t : ℝ}
    (ht : 0 ≤ (t - c) / (a - c)) :
    ‖quadraticLevelScaling a c x t‖ ^ 2 = (t - c) / (a - c) * ‖x‖ ^ 2 := by
  rw [quadraticLevelScaling, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ht]

theorem hasDerivAt_quadraticLevelScaling (a c : ℝ) (x : E) {t : ℝ}
    (ht : 0 < (t - c) / (a - c)) :
    HasDerivAt (quadraticLevelScaling a c x)
      ((2 * (t - c))⁻¹ • quadraticLevelScaling a c x t) t := by
  have hden : a - c ≠ 0 := by
    intro h
    rw [h, div_zero] at ht
    exact (lt_irrefl 0 ht)
  have hnum : t - c ≠ 0 := by
    intro h
    rw [h, zero_div] at ht
    exact (lt_irrefl 0 ht)
  have hsqrt : Real.sqrt ((t - c) / (a - c)) ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hsq := Real.sq_sqrt ht.le
  have hinner : HasDerivAt (fun s : ℝ => (s - c) / (a - c)) (1 / (a - c)) t :=
    ((hasDerivAt_id t).sub_const c).div_const (a - c)
  have hd := (hinner.sqrt ht.ne').smul_const x
  convert! hd using 1
  rw [quadraticLevelScaling, smul_smul]
  congr 1
  field_simp
  rw [hsq]
  field_simp

theorem isIntegralCurveOn_quadraticLevelScaling (a c : ℝ) (x : E) :
    IsIntegralCurveOn (quadraticLevelScaling a c x)
      (fun t y => (2 * (t - c))⁻¹ • y) {t | 0 < (t - c) / (a - c)} :=
  fun _ ht => (hasDerivAt_quadraticLevelScaling a c x ht).hasDerivWithinAt

theorem contDiffOn_quadraticLevelVectorField (c : ℝ) :
    ContDiffOn ℝ ∞ (quadraticLevelVectorField (E := E) c) {p | p.1 ≠ c} := by
  intro p hp
  exact (((contDiffAt_const.mul (contDiffAt_fst.sub contDiffAt_const)).inv
    (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hp))).smul contDiffAt_snd).contDiffWithinAt

theorem continuous_quadraticLevelScaling (a c : ℝ) :
    Continuous (fun p : ℝ × E => quadraticLevelScaling a c p.2 p.1) :=
  (Real.continuous_sqrt.comp ((continuous_fst.sub continuous_const).div_const _)).smul
    continuous_snd

theorem contDiffOn_quadraticLevelScaling (a c : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => quadraticLevelScaling a c p.2 p.1)
      {p | 0 < (p.1 - c) / (a - c)} := by
  intro p hp
  exact (((contDiffAt_fst.sub contDiffAt_const).div_const (a - c)).sqrt hp.ne').smul
    contDiffAt_snd |>.contDiffWithinAt

theorem quadraticLevelScaling_image_closedBall (a c : ℝ) {t : ℝ}
    (ht : 0 < (t - c) / (a - c)) (R : ℝ) :
    (fun x : E => quadraticLevelScaling a c x t) '' Metric.closedBall 0 R =
      Metric.closedBall 0 (Real.sqrt ((t - c) / (a - c)) * R) := by
  change Real.sqrt ((t - c) / (a - c)) • Metric.closedBall (0 : E) R = _
  rw [smul_closedBall' (Real.sqrt_pos.mpr ht).ne', smul_zero,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem quadraticLevelScaling_image_sphere (a c : ℝ) {t : ℝ}
    (ht : 0 < (t - c) / (a - c)) (R : ℝ) :
    (fun x : E => quadraticLevelScaling a c x t) '' Metric.sphere 0 R =
      Metric.sphere 0 (Real.sqrt ((t - c) / (a - c)) * R) := by
  change Real.sqrt ((t - c) / (a - c)) • Metric.sphere (0 : E) R = _
  rw [smul_sphere' (Real.sqrt_pos.mpr ht).ne', smul_zero,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem quadraticLevelScaling_height {a c α : ℝ} (hac : a ≠ c) {x : E}
    (hx : c + α / 2 * ‖x‖ ^ 2 = a) {t : ℝ} (ht : 0 ≤ (t - c) / (a - c)) :
    c + α / 2 * ‖quadraticLevelScaling a c x t‖ ^ 2 = t := by
  rw [norm_sq_quadraticLevelScaling a c x ht]
  have hden := sub_ne_zero.mpr hac
  calc
    c + α / 2 * ((t - c) / (a - c) * ‖x‖ ^ 2) =
        c + (t - c) / (a - c) * (α / 2 * ‖x‖ ^ 2) := by ring
    _ = c + (t - c) / (a - c) * (a - c) := by
      rw [show α / 2 * ‖x‖ ^ 2 = a - c by linarith]
    _ = t := by rw [div_mul_cancel₀ _ hden]; ring

theorem quadraticRadialCurve_eq_quadraticLevelScaling {a c α : ℝ} (hac : a ≠ c) {x : E}
    (hx : c + α / 2 * ‖x‖ ^ 2 = a) (t : ℝ) :
    quadraticRadialCurve (-α⁻¹) x (a - t) = quadraticLevelScaling a c x t := by
  have hα : α ≠ 0 := by
    intro h
    rw [h, zero_div, zero_mul, add_zero] at hx
    exact hac hx.symm
  have hnorm : ‖x‖ ^ 2 = 2 * (a - c) / α := by
    apply (eq_div_iff hα).mpr
    nlinarith [hx]
  simp only [quadraticRadialCurve, quadraticLevelScaling]
  congr 2
  rw [hnorm]
  field_simp
  ring

theorem quadraticLevelScaling_eq_smul_of_sq {a c t r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (h : R ^ 2 = (t - c) / (a - c) * r ^ 2) (x : E) :
    quadraticLevelScaling a c x t = (R / r) • x := by
  have heq : (t - c) / (a - c) = (R / r) ^ 2 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hr.ne')]
    exact h.symm
  rw [quadraticLevelScaling, heq, Real.sqrt_sq (div_nonneg hR hr.le)]

theorem quadraticLevelScaling_smul_div_of_sq {a c t r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (h : R ^ 2 = (t - c) / (a - c) * r ^ 2) (x : E) :
    quadraticLevelScaling a c ((r / R) • x) t = x := by
  rw [quadraticLevelScaling_eq_smul_of_sq hr hR.le h, smul_smul]
  have heq : R / r * (r / R) = 1 := by field_simp
  rw [heq, one_smul]

theorem quadraticLevelScaling_comp
    {a b c t : ℝ} (hbc : b ≠ c) (ht : 0 ≤ (t - c) / (b - c)) (x : E) :
    quadraticLevelScaling b c (quadraticLevelScaling a c x b) t =
      quadraticLevelScaling a c x t := by
  simp only [quadraticLevelScaling, smul_smul]
  rw [← Real.sqrt_mul ht, div_mul_div_cancel₀ (sub_ne_zero.mpr hbc)]

theorem quadraticLevelScaling_conjugacy_of_model
    (D Φ : ℝ → E → E) (G : E → E)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b < c)
    (hΦa : ∀ y, Φ a y = y)
    (hmodel : ∀ t ≤ b, ∀ x, D t (quadraticLevelScaling b c x t) = Φ t (G x))
    {t : ℝ} (ht : t ≤ b) (x : E) :
    D t (quadraticLevelScaling a c x t) = Φ t (D a x) := by
  have hac := hab.trans_lt hbc
  let y := quadraticLevelScaling a c x b
  have ha := hmodel a hab y
  rw [quadraticLevelScaling_comp hbc.ne
      (div_nonneg_of_nonpos (sub_neg.mpr hac).le (sub_neg.mpr hbc).le),
    quadraticLevelScaling_self hac.ne, hΦa] at ha
  rw [ha, ← hmodel t ht y]
  congr 1
  exact (quadraticLevelScaling_comp hbc.ne
    (div_nonneg_of_nonpos (sub_nonpos.mpr (ht.trans hbc.le)) (sub_neg.mpr hbc).le) x).symm

theorem image_sphere_and_closedBall_of_quadratic_cap_model
    {F : Type*} (D : E → F) (G : E → F) {a b c r : ℝ}
    (hab : a ≤ b) (hr : 0 < r) (hb : b = c - r ^ 2 / 2)
    (hmodel : ∀ x, D (quadraticLevelScaling b c x a) = G x) :
    let R := Real.sqrt (2 * (c - a))
    0 < R ∧ R ^ 2 = 2 * (c - a) ∧
      D '' Metric.sphere 0 R = G '' Metric.sphere 0 r ∧
      D '' Metric.closedBall 0 R = G '' Metric.closedBall 0 r := by
  have hbc : b < c := by rw [hb]; nlinarith [sq_pos_of_pos hr]
  have hac := hab.trans_lt hbc
  have hratio : 0 < (a - c) / (b - c) :=
    div_pos_of_neg_of_neg (sub_neg.mpr hac) (sub_neg.mpr hbc)
  have hrad : Real.sqrt ((a - c) / (b - c)) * r = Real.sqrt (2 * (c - a)) := by
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hr.le) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hratio.le, Real.sq_sqrt (by linarith : 0 ≤ 2 * (c - a)),
      div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hbc.ne), hb]
    ring
  have hf : (D ∘ fun x => quadraticLevelScaling b c x a) = G := funext hmodel
  refine ⟨Real.sqrt_pos.mpr (by linarith), Real.sq_sqrt (by linarith), ?_, ?_⟩
  · rw [← hrad, ← quadraticLevelScaling_image_sphere b c hratio r, image_image]
    exact congrArg (fun f : E → F => f '' Metric.sphere 0 r) hf
  · rw [← hrad, ← quadraticLevelScaling_image_closedBall b c hratio r, image_image]
    exact congrArg (fun f : E → F => f '' Metric.closedBall 0 r) hf

end DifferentialGeometry.Analysis.ODE
