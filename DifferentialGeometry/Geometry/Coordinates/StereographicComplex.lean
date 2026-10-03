import DifferentialGeometry.Geometry.Coordinates.Stereographic
import Mathlib.Topology.OpenPartialHomeomorph.Basic

noncomputable section

namespace DifferentialGeometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def sphereNorthPole : Metric.sphere (0 : E3) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp [EuclideanSpace.single]⟩

theorem sphereNorthPole_coe : (sphereNorthPole : E3) = EuclideanSpace.single 0 1 := rfl

private theorem norm_sphereNorthPole : ‖(sphereNorthPole : E3)‖ = 1 := by
  simp [sphereNorthPole, EuclideanSpace.single]

private theorem northPole_inner (x : E3) : inner ℝ (sphereNorthPole : E3) x = x 0 := by
  simp only [sphereNorthPole_coe, EuclideanSpace.inner_single_left, map_one, one_mul]

private theorem northPole_orthogonal_zero (x : (ℝ ∙ (sphereNorthPole : E3))ᗮ) :
    (x : E3) 0 = 0 := by
  have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  rwa [northPole_inner] at h

def northPoleOrthogonalComplex : (ℝ ∙ (sphereNorthPole : E3))ᗮ ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv :=
    { toFun := fun x => ⟨(x : E3) 1, (x : E3) 2⟩
      invFun := fun z => ⟨WithLp.toLp 2 ![0, z.re, z.im], by
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        rw [northPole_inner]
        rfl⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply PiLp.ext
        intro i
        fin_cases i
        · exact (northPole_orthogonal_zero x).symm
        · rfl
        · rfl
      right_inv := by intro z; apply Complex.ext <;> rfl
      map_add' := by
        intro x y
        apply Complex.ext <;> rfl
      map_smul' := by
        intro c x
        apply Complex.ext <;>
          simp only [Submodule.coe_smul, PiLp.smul_apply, RingHom.id_apply,
            Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero, add_zero, smul_eq_mul] }
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(⟨(x : E3) 1, (x : E3) 2⟩ : ℂ)‖ ^ 2 = ‖(x : E3)‖ ^ 2
    rw [Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (x : E3) 1 * (x : E3) 1 + (x : E3) 2 * (x : E3) 2 =
      (x : E3) 0 ^ 2 + ((x : E3) 1 ^ 2 + (x : E3) 2 ^ 2)
    rw [northPole_orthogonal_zero]
    ring

@[simp]
theorem northPoleOrthogonalComplex_apply (x : (ℝ ∙ (sphereNorthPole : E3))ᗮ) :
    northPoleOrthogonalComplex x = ((x : E3) 1 : ℂ) + ((x : E3) 2 : ℂ) * Complex.I := by
  change (⟨(x : E3) 1, (x : E3) 2⟩ : ℂ) = _
  apply Complex.ext <;> simp

@[simp]
theorem northPoleOrthogonalComplex_symm_coe (z : ℂ) :
    (northPoleOrthogonalComplex.symm z : E3) = WithLp.toLp 2 ![0, z.re, z.im] := rfl

def stereographicComplex :
    {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole} ≃ₜ ℂ :=
  ((stereographic norm_sphereNorthPole).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)).trans northPoleOrthogonalComplex.toHomeomorph

theorem stereographicComplex_eq_stereographic
    (ξ : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
    stereographicComplex ξ = northPoleOrthogonalComplex
      (stereographic norm_sphereNorthPole ξ.val) := rfl

private theorem northPole_orthogonalProjection_coe (x : E3) :
    ((ℝ ∙ (sphereNorthPole : E3))ᗮ.orthogonalProjectionOnto x : E3) =
      x - x 0 • (sphereNorthPole : E3) := by
  rw [Submodule.orthogonalProjectionOnto_orthogonal]
  change x - (ℝ ∙ (sphereNorthPole : E3)).starProjection x = _
  rw [Submodule.starProjection_unit_singleton ℝ norm_sphereNorthPole, northPole_inner]

theorem stereographicComplex_apply
    (ξ : {ξ : Metric.sphere (0 : E3) 1 // ξ ≠ sphereNorthPole}) :
    stereographicComplex ξ = ((2 / (1 - (ξ.val : E3) 0) : ℝ) : ℂ) *
      (((ξ.val : E3) 1 : ℂ) + ((ξ.val : E3) 2 : ℂ) * Complex.I) := by
  rw [stereographicComplex_eq_stereographic, stereographic_apply, map_smul,
    northPoleOrthogonalComplex_apply, northPole_inner, northPole_orthogonalProjection_coe]
  apply Complex.ext <;>
    simp [sphereNorthPole, EuclideanSpace.single, smul_eq_mul] <;> ring

theorem stereographicComplex_symm_coe (z : ℂ) :
    ((stereographicComplex.symm z).val : E3) = WithLp.toLp 2
      ![(‖z‖ ^ 2 - 4) / (‖z‖ ^ 2 + 4),
        4 * z.re / (‖z‖ ^ 2 + 4), 4 * z.im / (‖z‖ ^ 2 + 4)] := by
  change (stereoInvFun norm_sphereNorthPole (northPoleOrthogonalComplex.symm z) : E3) = _
  rw [stereoInvFun_apply]
  have hn : ‖northPoleOrthogonalComplex.symm z‖ = ‖z‖ :=
    northPoleOrthogonalComplex.symm.norm_map z
  rw [hn, northPoleOrthogonalComplex_symm_coe, sphereNorthPole_coe]
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [EuclideanSpace.single, smul_eq_mul, div_eq_mul_inv] <;> ring

theorem dist_stereographicComplex_symm_sq (z w : ℂ) :
    dist (stereographicComplex.symm z).val (stereographicComplex.symm w).val ^ 2 =
      16 * dist z w ^ 2 / ((‖z‖ ^ 2 + 4) * (‖w‖ ^ 2 + 4)) := by
  change dist (stereoInvFun norm_sphereNorthPole (northPoleOrthogonalComplex.symm z))
    (stereoInvFun norm_sphereNorthPole (northPoleOrthogonalComplex.symm w)) ^ 2 = _
  rw [dist_stereoInvFun_sq, northPoleOrthogonalComplex.symm.dist_map,
    northPoleOrthogonalComplex.symm.norm_map, northPoleOrthogonalComplex.symm.norm_map]

theorem dist_stereographicComplex_symm_northPole_sq (z : ℂ) :
    dist (stereographicComplex.symm z).val sphereNorthPole ^ 2 =
      16 / (‖z‖ ^ 2 + 4) := by
  change dist (stereoInvFun norm_sphereNorthPole (northPoleOrthogonalComplex.symm z) : E3)
    (sphereNorthPole : E3) ^ 2 = _
  rw [dist_stereoInvFun_pole_sq, northPoleOrthogonalComplex.symm.norm_map]

theorem dist_stereographicComplex_symm_neg_northPole_sq (z : ℂ) :
    dist (stereographicComplex.symm z).val (-sphereNorthPole) ^ 2 =
      4 * ‖z‖ ^ 2 / (‖z‖ ^ 2 + 4) := by
  change dist (stereoInvFun norm_sphereNorthPole (northPoleOrthogonalComplex.symm z) : E3)
    (-(sphereNorthPole : E3)) ^ 2 = _
  rw [dist_stereoInvFun_neg_pole_sq, northPoleOrthogonalComplex.symm.norm_map]

end DifferentialGeometry
