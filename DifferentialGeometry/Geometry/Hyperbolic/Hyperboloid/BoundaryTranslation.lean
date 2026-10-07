import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Boundary
import DifferentialGeometry.Geometry.Coordinates.StereographicComplex

noncomputable section

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private def translationShift (b : ℂ) (v : ℝ × E3) : ℝ :=
  b.re / 2 * v.2 1 + b.im / 2 * v.2 2 + (b.re ^ 2 + b.im ^ 2) / 8 * (v.1 - v.2 0)

private def translationLinear (b : ℂ) : (ℝ × E3) →ₗ[ℝ] ℝ × E3 where
  toFun v := (v.1 + translationShift b v, WithLp.toLp 2
    ![v.2 0 + translationShift b v,
      v.2 1 + b.re / 2 * (v.1 - v.2 0), v.2 2 + b.im / 2 * (v.1 - v.2 0)])
  map_add' v w := by
    apply Prod.ext
    · simp [translationShift]
      ring
    · apply PiLp.ext
      intro i
      fin_cases i <;> simp [translationShift, PiLp.add_apply] <;> ring
  map_smul' c v := by
    apply Prod.ext
    · simp [translationShift, smul_eq_mul]
      ring
    · apply PiLp.ext
      intro i
      fin_cases i <;> simp [translationShift, PiLp.smul_apply, smul_eq_mul] <;> ring

private theorem translationLinear_neg_leftInverse (b : ℂ) (v : ℝ × E3) :
    translationLinear (-b) (translationLinear b v) = v := by
  apply Prod.ext
  · simp [translationLinear, translationShift]
    ring
  · apply PiLp.ext
    intro i
    fin_cases i <;> simp [translationLinear, translationShift] <;> ring

private theorem translationLinear_preserves (b : ℂ) (v w : ℝ × E3) :
    lorentzForm E3 (translationLinear b v) (translationLinear b w) = lorentzForm E3 v w := by
  simp only [lorentzForm_apply, PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, Real.inner_apply]
  simp [translationLinear, translationShift]
  ring

private def translationLorentz (b : ℂ) :
    (lorentzForm E3).IsometryEquiv (lorentzForm E3) where
  toLinearEquiv :=
    { translationLinear b with
      invFun := translationLinear (-b)
      left_inv := translationLinear_neg_leftInverse b
      right_inv := by
        intro v
        change translationLinear b (translationLinear (-b) v) = v
        simpa only [neg_neg] using translationLinear_neg_leftInverse (-b) v }
  map_app' := translationLinear_preserves b

private theorem translationLorentz_origin_time_pos (b : ℂ) :
    0 < (translationLorentz b (1, 0)).1 := by
  change 0 < 1 + translationShift b (1, 0)
  simp only [translationShift, PiLp.zero_apply, mul_zero, add_zero, sub_zero, mul_one]
  positivity

def boundaryTranslation (b : ℂ) : Hyperboloid E3 ≃ᵢ Hyperboloid E3 :=
  lorentzIsometryEquiv (translationLorentz b) (translationLorentz_origin_time_pos b)

theorem boundaryTranslation_coordinates (b : ℂ) (x : Hyperboloid E3) :
    let l := x.time - x.space 0
    let k := b.re / 2 * x.space 1 + b.im / 2 * x.space 2 + (b.re ^ 2 + b.im ^ 2) / 8 * l
    ((boundaryTranslation b x).time, (boundaryTranslation b x).space) =
      (x.time + k, WithLp.toLp 2
        ![x.space 0 + k, x.space 1 + b.re / 2 * l, x.space 2 + b.im / 2 * l]) := rfl

private theorem lorentzExtension_boundaryTranslation (b : ℂ) :
    lorentzExtension (boundaryTranslation b) = translationLorentz b := by
  apply (exists_unique_lorentz_extension (boundaryTranslation b)).unique
    (lorentzExtension_apply _)
  intro x
  rfl

@[simp] theorem boundaryHomeomorph_boundaryTranslation_northPole (b : ℂ) :
    boundaryHomeomorph (boundaryTranslation b) sphereNorthPole = sphereNorthPole := by
  apply Subtype.ext
  rw [boundaryHomeomorph_apply_coe, lorentzExtension_boundaryTranslation]
  change (translationLinear b (1, (sphereNorthPole : E3))).1⁻¹ •
    (translationLinear b (1, (sphereNorthPole : E3))).2 = (sphereNorthPole : E3)
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [translationLinear, translationShift,
    sphereNorthPole_coe, EuclideanSpace.single]

private theorem northPole_denominator_ne_zero
    (ξ : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
    1 - (ξ.val : E3) 0 ≠ 0 := by
  intro hz
  have hcoord : (ξ.val : E3) 0 = 1 := by linarith
  have hi : inner ℝ (sphereNorthPole : E3) (ξ.val : E3) = 1 := by
    simp only [sphereNorthPole_coe, EuclideanSpace.inner_single_left, map_one, one_mul, hcoord]
  have heq := (inner_eq_one_iff_of_norm_eq_one
    (norm_eq_of_mem_sphere sphereNorthPole) (norm_eq_of_mem_sphere ξ.val)).mp hi
  exact ξ.property (Subtype.ext heq.symm)

theorem stereographicComplex_boundaryTranslation (b : ℂ)
    (ξ : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
    stereographicComplex
      ⟨boundaryHomeomorph (boundaryTranslation b) ξ.val, by
        intro hp
        apply ξ.property
        apply (boundaryHomeomorph (boundaryTranslation b)).injective
        rw [boundaryHomeomorph_boundaryTranslation_northPole]
        exact hp⟩ = stereographicComplex ξ + b := by
  let v : ℝ × E3 := (1, (ξ.val : E3))
  let k := translationShift b v
  have ht : 1 + k ≠ 0 := by
    have hp := lorentzExtension_sphere_time_pos (boundaryTranslation b) ξ.val
    rw [lorentzExtension_boundaryTranslation] at hp
    change 0 < 1 + k at hp
    exact hp.ne'
  have hd := northPole_denominator_ne_zero ξ
  have hden : 1 - (1 + k)⁻¹ * ((ξ.val : E3) 0 + k) =
      (1 - (ξ.val : E3) 0) / (1 + k) := by
    field_simp [ht]
    ring
  rw [stereographicComplex_apply, stereographicComplex_apply]
  rw [boundaryHomeomorph_apply_coe, lorentzExtension_boundaryTranslation]
  change (((2 / (1 - (1 + k)⁻¹ * ((ξ.val : E3) 0 + k)) : ℝ) : ℂ) *
      (((1 + k)⁻¹ * ((ξ.val : E3) 1 + b.re / 2 * (1 - (ξ.val : E3) 0)) : ℝ) +
        (((1 + k)⁻¹ * ((ξ.val : E3) 2 + b.im / 2 * (1 - (ξ.val : E3) 0)) : ℝ) : ℂ) * Complex.I)) = _
  rw [hden]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add]
  all_goals
    field_simp [ht, hd]

theorem boundaryHomeomorph_boundaryTranslation_stereographicComplex_symm (b z : ℂ) :
    boundaryHomeomorph (boundaryTranslation b) (stereographicComplex.symm z).val =
      (stereographicComplex.symm (z + b)).val := by
  let ξ := stereographicComplex.symm z
  let η : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole} :=
    ⟨boundaryHomeomorph (boundaryTranslation b) ξ.val, by
      intro hp
      apply ξ.property
      apply (boundaryHomeomorph (boundaryTranslation b)).injective
      rw [boundaryHomeomorph_boundaryTranslation_northPole]
      exact hp⟩
  have hη : stereographicComplex η = z + b := by
    simpa only [ξ, stereographicComplex.apply_symm_apply] using
      stereographicComplex_boundaryTranslation b ξ
  have heq : η = stereographicComplex.symm (z + b) :=
    stereographicComplex.injective (hη.trans (stereographicComplex.apply_symm_apply _).symm)
  exact congrArg Subtype.val heq

end DifferentialGeometry.Hyperboloid
