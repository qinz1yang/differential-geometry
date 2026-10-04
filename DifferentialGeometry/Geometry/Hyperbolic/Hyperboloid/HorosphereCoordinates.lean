import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Defs
import DifferentialGeometry.Geometry.Coordinates.StereographicComplex

noncomputable section

namespace DifferentialGeometry.Hyperboloid

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private def horospherePoint (h : ℝ) (hh : 0 < h) (z : ℂ) : Hyperboloid E₃ where
  time := h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8
  space := WithLp.toLp 2 ![-h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8,
    h / 2 * z.re, h / 2 * z.im]
  time_pos := by positivity
  time_sq_sub_inner_self := by
    simp only [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
      add_zero, Real.inner_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
    rw [Complex.sq_norm, Complex.normSq_apply]
    field_simp
    ring

private theorem horospherePoint_height (h : ℝ) (hh : 0 < h) (z : ℂ) :
    (horospherePoint h hh z).time - (horospherePoint h hh z).space 0 = h := by
  change (h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8) -
    (-h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8) = h
  ring

private def horosphereCoordinate (h : ℝ) (x : Hyperboloid E₃) : ℂ :=
  (2 / h : ℝ) • (⟨x.space 1, x.space 2⟩ : ℂ)

private theorem horosphereCoordinate_point (h : ℝ) (hh : 0 < h) (z : ℂ) :
    horosphereCoordinate h (horospherePoint h hh z) = z := by
  apply Complex.ext <;> simp only [horosphereCoordinate, horospherePoint, Complex.smul_re,
    Complex.smul_im, smul_eq_mul] <;> change 2 / h * (h / 2 * _) = _ <;> field_simp

private theorem horospherePoint_coordinate (h : ℝ) (hh : 0 < h)
    (x : {x : Hyperboloid E₃ // x.time - x.space 0 = h}) :
    horospherePoint h hh (horosphereCoordinate h x.val) = x.val := by
  have hsheet := x.val.time_sq_sub_inner_self
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, Real.inner_apply] at hsheet
  change x.val.time ^ 2 - (x.val.space 0 * x.val.space 0 +
    (x.val.space 1 * x.val.space 1 + x.val.space 2 * x.val.space 2)) = 1 at hsheet
  have hheight := x.property
  have hrel : h ^ 2 + 2 * h * x.val.space 0 =
      1 + x.val.space 1 ^ 2 + x.val.space 2 ^ 2 := by
    have ht : x.val.time = h + x.val.space 0 := by linarith
    rw [ht] at hsheet
    nlinarith only [hsheet]
  apply Hyperboloid.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · change -h / 2 + 1 / (2 * h) + h * ‖horosphereCoordinate h x.val‖ ^ 2 / 8 = x.val.space 0
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [horosphereCoordinate, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    field_simp
    nlinarith only [hrel]
  · change h / 2 * (horosphereCoordinate h x.val).re = x.val.space 1
    simp only [horosphereCoordinate, Complex.smul_re, smul_eq_mul]
    field_simp
  · change h / 2 * (horosphereCoordinate h x.val).im = x.val.space 2
    simp only [horosphereCoordinate, Complex.smul_im, smul_eq_mul]
    field_simp

private theorem continuous_horosphereCoordinate (h : ℝ) : Continuous (horosphereCoordinate h) := by
  have h₁ := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp
    (continuous_space (E := E₃))
  have h₂ := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).comp
    (continuous_space (E := E₃))
  have hc : Continuous (fun x : Hyperboloid E₃ =>
      ((x.space 1 : ℝ) : ℂ) + ((x.space 2 : ℝ) : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp h₁).add ((Complex.continuous_ofReal.comp h₂).mul continuous_const)
  have he : (fun x : Hyperboloid E₃ => (⟨x.space 1, x.space 2⟩ : ℂ)) =
      fun x => ((x.space 1 : ℝ) : ℂ) + ((x.space 2 : ℝ) : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp
  unfold horosphereCoordinate
  exact (continuous_const : Continuous (fun _ : Hyperboloid E₃ => (2 / h : ℝ))).smul (he.symm ▸ hc)

private theorem continuous_horospherePoint (h : ℝ) (hh : 0 < h) :
    Continuous (horospherePoint h hh) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun z : ℂ =>
    (h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8,
      WithLp.toLp 2 ![-h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8,
        h / 2 * z.re, h / 2 * z.im]))
  fun_prop

def northPoleHorosphereHomeomorph (h : ℝ) (hh : 0 < h) :
    {x : Hyperboloid E₃ // x.time - x.space 0 = h} ≃ₜ ℂ where
  toFun x := horosphereCoordinate h x.val
  invFun z := ⟨horospherePoint h hh z, horospherePoint_height h hh z⟩
  left_inv x := Subtype.ext (horospherePoint_coordinate h hh x)
  right_inv := horosphereCoordinate_point h hh
  continuous_toFun := (continuous_horosphereCoordinate h).comp continuous_subtype_val
  continuous_invFun := (continuous_horospherePoint h hh).subtype_mk _

theorem northPoleHorosphereHomeomorph_apply (h : ℝ) (hh : 0 < h)
    (x : {x : Hyperboloid E₃ // x.time - x.space 0 = h}) :
    northPoleHorosphereHomeomorph h hh x =
      ((2 / h : ℝ) : ℂ) * ((x.val.space 1 : ℂ) + (x.val.space 2 : ℂ) * Complex.I) := by
  apply Complex.ext <;> simp [northPoleHorosphereHomeomorph, horosphereCoordinate]

theorem northPoleHorosphereHomeomorph_symm_coordinates (h : ℝ) (hh : 0 < h) (z : ℂ) :
    (((northPoleHorosphereHomeomorph h hh).symm z).val.time,
      ((northPoleHorosphereHomeomorph h hh).symm z).val.space) =
      (h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8,
        WithLp.toLp 2 ![-h / 2 + 1 / (2 * h) + h * ‖z‖ ^ 2 / 8,
          h / 2 * z.re, h / 2 * z.im]) := rfl

end DifferentialGeometry.Hyperboloid
