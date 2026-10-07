import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryPlaneAffine
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryTranslation
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Geometry.Euclidean.Inversion.Basic

noncomputable section

namespace DifferentialGeometry.Hyperboloid

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

private def northReflection : E3 ≃ₗᵢ[ℝ] E3 :=
  (ℝ ∙ (sphereNorthPole : E3))ᗮ.reflection

private theorem northReflection_apply (x : E3) :
    northReflection x = WithLp.toLp 2 ![-x 0, x 1, x 2] := by
  have hn : ‖(sphereNorthPole : E3)‖ = 1 := norm_eq_of_mem_sphere _
  have hi : inner ℝ (sphereNorthPole : E3) x = x 0 := by
    simp only [sphereNorthPole_coe, EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [northReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, hn, hi]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [sphereNorthPole_coe, EuclideanSpace.single, smul_eq_mul]
  ring

private def northInversion : Hyperboloid E3 ≃ᵢ Hyperboloid E3 :=
  lorentzIsometryEquiv (spatialLorentzEquiv northReflection) (by change (0 : ℝ) < 1; norm_num)

private theorem northInversion_extension :
    lorentzExtension northInversion = spatialLorentzEquiv northReflection := by
  apply (exists_unique_lorentz_extension northInversion).unique (lorentzExtension_apply _)
  intro x
  rfl

private theorem northInversion_boundary_coe (ξ : S2) :
    (boundaryHomeomorph northInversion ξ : E3) = northReflection (ξ : E3) := by
  rw [boundaryHomeomorph_apply_coe, northInversion_extension]
  change (1 : ℝ)⁻¹ • northReflection (ξ : E3) = northReflection (ξ : E3)
  rw [inv_one, one_smul]

private theorem northInversion_boundary_involutive (ξ : S2) :
    boundaryHomeomorph northInversion (boundaryHomeomorph northInversion ξ) = ξ := by
  apply Subtype.ext
  rw [northInversion_boundary_coe, northInversion_boundary_coe]
  exact (ℝ ∙ (sphereNorthPole : E3))ᗮ.reflection_reflection (ξ : E3)

private theorem northInversion_boundary_north :
    boundaryHomeomorph northInversion sphereNorthPole = (stereographicComplex.symm 0).val := by
  apply Subtype.ext
  rw [northInversion_boundary_coe, northReflection_apply, stereographicComplex_symm_coe]
  apply PiLp.ext
  intro i
  fin_cases i <;> norm_num [sphereNorthPole_coe, EuclideanSpace.single]

private theorem northInversion_boundary_zero :
    boundaryHomeomorph northInversion (stereographicComplex.symm 0).val = sphereNorthPole := by
  rw [← northInversion_boundary_north, northInversion_boundary_involutive]

private theorem inversion_zero_two (z : ℂ) :
    EuclideanGeometry.inversion (0 : ℂ) 2 z = (4 / ‖z‖ ^ 2 : ℝ) • z := by
  simp only [EuclideanGeometry.inversion, dist_zero_right, vsub_eq_sub, sub_zero,
    vadd_eq_add, add_zero]
  congr 1
  norm_num [div_pow]

private theorem northInversion_boundary_stereographic (z : ℂ) (hz : z ≠ 0) :
    boundaryHomeomorph northInversion (stereographicComplex.symm z).val =
      (stereographicComplex.symm (EuclideanGeometry.inversion (0 : ℂ) 2 z)).val := by
  have hnonpole : boundaryHomeomorph northInversion (stereographicComplex.symm z).val ≠
      sphereNorthPole := by
    intro hp
    have h := (boundaryHomeomorph northInversion).injective
      (hp.trans northInversion_boundary_zero.symm)
    exact hz (stereographicComplex.symm.injective (Subtype.ext h))
  let ξ : {ξ : S2 // ξ ≠ sphereNorthPole} :=
    ⟨boundaryHomeomorph northInversion (stereographicComplex.symm z).val, hnonpole⟩
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hd : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  have hchart : stereographicComplex ξ = EuclideanGeometry.inversion (0 : ℂ) 2 z := by
    rw [stereographicComplex_apply, inversion_zero_two]
    change ((2 / (1 - ((boundaryHomeomorph northInversion
        (stereographicComplex.symm z).val : E3) 0)) : ℝ) : ℂ) *
      ((((boundaryHomeomorph northInversion (stereographicComplex.symm z).val : E3) 1) : ℂ) +
        (((boundaryHomeomorph northInversion (stereographicComplex.symm z).val : E3) 2) : ℂ) *
          Complex.I) = _
    rw [northInversion_boundary_coe, northReflection_apply, stereographicComplex_symm_coe]
    change (((2 / (1 - (-((‖z‖ ^ 2 - 4) / (‖z‖ ^ 2 + 4)))) : ℝ) : ℂ) *
      (((4 * z.re / (‖z‖ ^ 2 + 4) : ℝ) : ℂ) +
        ((4 * z.im / (‖z‖ ^ 2 + 4) : ℝ) : ℂ) * Complex.I)) = _
    have hden : 1 - (-((‖z‖ ^ 2 - 4) / (‖z‖ ^ 2 + 4))) =
        2 * ‖z‖ ^ 2 / (‖z‖ ^ 2 + 4) := by
      field_simp [hd]
      ring
    rw [hden]
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add,
        Complex.smul_re, Complex.smul_im, smul_eq_mul]
    all_goals field_simp [hn, hd]
  have heq : ξ = stereographicComplex.symm (EuclideanGeometry.inversion (0 : ℂ) 2 z) :=
    stereographicComplex.injective (hchart.trans (stereographicComplex.apply_symm_apply _).symm)
  exact congrArg Subtype.val heq

private theorem inverse_north_ne (e : Hyperboloid E3 ≃ᵢ Hyperboloid E3)
    (he : boundaryHomeomorph e sphereNorthPole ≠ sphereNorthPole) :
    (boundaryHomeomorph e).symm sphereNorthPole ≠ sphereNorthPole := by
  intro h
  apply he
  calc
    boundaryHomeomorph e sphereNorthPole =
        boundaryHomeomorph e ((boundaryHomeomorph e).symm sphereNorthPole) :=
      congrArg (boundaryHomeomorph e) h.symm
    _ = sphereNorthPole := (boundaryHomeomorph e).apply_symm_apply _

theorem exists_stereographicComplex_inversion_similarity
    (e : Hyperboloid E3 ≃ᵢ Hyperboloid E3)
    (he : boundaryHomeomorph e sphereNorthPole ≠ sphereNorthPole) :
    let a := stereographicComplex
      ⟨(boundaryHomeomorph e).symm sphereNorthPole, inverse_north_ne e he⟩
    let b := stereographicComplex ⟨boundaryHomeomorph e sphereNorthPole, he⟩
    ∃ s : ℝ, 0 < s ∧ ∃ Q : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ z : ℂ, z ≠ a →
      boundaryHomeomorph e (stereographicComplex.symm z).val =
        (stereographicComplex.symm
          (b + s • Q (EuclideanGeometry.inversion (0 : ℂ) 2 (z - a)))).val := by
  let a := stereographicComplex
    ⟨(boundaryHomeomorph e).symm sphereNorthPole, inverse_north_ne e he⟩
  let b := stereographicComplex ⟨boundaryHomeomorph e sphereNorthPole, he⟩
  have ha : (stereographicComplex.symm a).val =
      (boundaryHomeomorph e).symm sphereNorthPole :=
    congrArg Subtype.val (stereographicComplex.symm_apply_apply _)
  let F := northInversion.trans ((boundaryTranslation a).trans e)
  have hFn : boundaryHomeomorph F sphereNorthPole = sphereNorthPole := by
    simp only [F, boundaryHomeomorph_trans, Homeomorph.trans_apply]
    rw [northInversion_boundary_north,
      boundaryHomeomorph_boundaryTranslation_stereographicComplex_symm, zero_add, ha]
    exact (boundaryHomeomorph e).apply_symm_apply _
  have hF0 : boundaryHomeomorph F (stereographicComplex.symm 0).val =
      boundaryHomeomorph e sphereNorthPole := by
    simp only [F, boundaryHomeomorph_trans, Homeomorph.trans_apply]
    rw [northInversion_boundary_zero, boundaryHomeomorph_boundaryTranslation_northPole]
  let H : ℂ → ℂ := fun z => stereographicComplex
    ⟨boundaryHomeomorph F (stereographicComplex.symm z).val, by
      intro hp
      exact (stereographicComplex.symm z).property
        ((boundaryHomeomorph F).injective (hp.trans hFn.symm))⟩
  have hH0 : H 0 = b := by
    apply congrArg stereographicComplex
    apply Subtype.ext
    exact hF0
  let s := (lorentzExtension F (1, (sphereNorthPole : E3))).1
  obtain ⟨Q, hQ⟩ := exists_stereographicComplex_similarity F hFn
  change ∀ z : ℂ, H z = s • Q z + H 0 at hQ
  have hF (w : ℂ) : boundaryHomeomorph F (stereographicComplex.symm w).val =
      (stereographicComplex.symm (b + s • Q w)).val := by
    let ξ : {ξ : S2 // ξ ≠ sphereNorthPole} :=
      ⟨boundaryHomeomorph F (stereographicComplex.symm w).val, by
        intro hp
        exact (stereographicComplex.symm w).property
          ((boundaryHomeomorph F).injective (hp.trans hFn.symm))⟩
    have hξ : stereographicComplex ξ = b + s • Q w := by
      change H w = _
      rw [hQ, hH0, add_comm]
    have heq : ξ = stereographicComplex.symm (b + s • Q w) :=
      stereographicComplex.injective (hξ.trans (stereographicComplex.apply_symm_apply _).symm)
    exact congrArg Subtype.val heq
  refine ⟨s, lorentzExtension_sphere_time_pos F sphereNorthPole, Q, ?_⟩
  intro z hz
  have hJ := northInversion_boundary_stereographic (z - a) (sub_ne_zero.mpr hz)
  calc
    boundaryHomeomorph e (stereographicComplex.symm z).val =
        boundaryHomeomorph e (boundaryHomeomorph (boundaryTranslation a)
          (stereographicComplex.symm (z - a)).val) := by
      rw [boundaryHomeomorph_boundaryTranslation_stereographicComplex_symm, sub_add_cancel]
    _ = boundaryHomeomorph F
        (boundaryHomeomorph northInversion (stereographicComplex.symm (z - a)).val) := by
      simp only [F, boundaryHomeomorph_trans, Homeomorph.trans_apply]
      rw [northInversion_boundary_involutive]
    _ = boundaryHomeomorph F
        (stereographicComplex.symm (EuclideanGeometry.inversion (0 : ℂ) 2 (z - a))).val := by
      rw [hJ]
    _ = _ := hF _

end DifferentialGeometry.Hyperboloid
