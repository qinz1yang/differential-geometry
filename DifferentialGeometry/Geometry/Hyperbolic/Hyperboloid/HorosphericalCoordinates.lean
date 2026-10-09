import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.HorosphereCoordinates
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Manifold
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

local notation "U" => (TopologicalSpace.Opens.mk (Set.ofPred (fun u : E₃ => 0 < u 0))
  (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0)))

private theorem northPoleHeight_pos (x : Hyperboloid E₃) : 0 < x.time - x.space 0 := by
  have hs := x.time_sq_sub_inner_self
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, Real.inner_apply] at hs
  nlinarith [x.time_pos, sq_nonneg (x.space 1), sq_nonneg (x.space 2)]

private def horosphericalCoordinate (x : Hyperboloid E₃) : U :=
  ⟨WithLp.toLp 2 ![x.time - x.space 0,
    2 * x.space 1 / (x.time - x.space 0), 2 * x.space 2 / (x.time - x.space 0)],
    northPoleHeight_pos x⟩

private def horosphericalPoint (u : U) : Hyperboloid E₃ :=
  ((northPoleHorosphereHomeomorph (u.val 0) u.property).symm
    ((u.val 1 : ℂ) + (u.val 2 : ℂ) * Complex.I)).val

private theorem horosphericalPoint_coordinate (x : Hyperboloid E₃) :
    horosphericalPoint (horosphericalCoordinate x) = x := by
  let h := x.time - x.space 0
  let y : {y : Hyperboloid E₃ // y.time - y.space 0 = h} := ⟨x, rfl⟩
  have hc : northPoleHorosphereHomeomorph h (northPoleHeight_pos x) y =
      (((horosphericalCoordinate x).val 1 : ℂ) +
        ((horosphericalCoordinate x).val 2 : ℂ) * Complex.I) := by
    rw [northPoleHorosphereHomeomorph_apply]
    change ((2 / h : ℝ) : ℂ) * ((x.space 1 : ℂ) + (x.space 2 : ℂ) * Complex.I) =
      ((2 * x.space 1 / h : ℝ) : ℂ) + ((2 * x.space 2 / h : ℝ) : ℂ) * Complex.I
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add] <;> ring
  change ((northPoleHorosphereHomeomorph h (northPoleHeight_pos x)).symm _).val = x
  rw [← hc]
  exact congrArg Subtype.val ((northPoleHorosphereHomeomorph h
    (northPoleHeight_pos x)).symm_apply_apply y)

private theorem horosphericalCoordinate_point (u : U) :
    horosphericalCoordinate (horosphericalPoint u) = u := by
  have hp := northPoleHorosphereHomeomorph_symm_coordinates (u.val 0) u.property
    ((u.val 1 : ℂ) + (u.val 2 : ℂ) * Complex.I)
  have ht := congrArg Prod.fst hp
  have hs := congrArg Prod.snd hp
  dsimp only at ht hs
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change (![_, _, _] : Fin 3 → ℝ) i = u.val i
  dsimp only [horosphericalPoint]
  rw [ht, hs]
  fin_cases i <;> simp [Complex.mul_re, Complex.mul_im]
  · ring
  · field_simp [(show 0 < u.val 0 from u.property).ne']
    ring
  · field_simp [(show 0 < u.val 0 from u.property).ne']
    ring

private theorem contDiff_euclideanCoordinate (i : Fin 3) :
    ContDiff ℝ ∞ (fun u : E₃ => u i) :=
  (contDiff_apply ℝ ℝ i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff

private theorem contMDiff_horosphericalCoordinate :
    ContMDiff 𝓘(ℝ, E₃) 𝓘(ℝ, E₃) ∞ horosphericalCoordinate := by
  apply (ContMDiff.subtypeVal_comp_iff U horosphericalCoordinate).mp
  have hc (i : Fin 3) : ContMDiff 𝓘(ℝ, E₃) 𝓘(ℝ, ℝ) ∞
      (fun x : Hyperboloid E₃ => x.space i) :=
    (contDiff_euclideanCoordinate i).contMDiff.comp contMDiff_space
  have hh := contMDiff_time.sub (hc 0)
  have hf : ContMDiff 𝓘(ℝ, E₃) 𝓘(ℝ, Fin 3 → ℝ) ∞
      (fun x : Hyperboloid E₃ => ![x.time - x.space 0,
        2 * x.space 1 / (x.time - x.space 0), 2 * x.space 2 / (x.time - x.space 0)]) := by
    apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · exact hh
    · exact (contMDiff_const.mul (hc 1)).div₀ hh (fun x => (northPoleHeight_pos x).ne')
    · exact (contMDiff_const.mul (hc 2)).div₀ hh (fun x => (northPoleHeight_pos x).ne')
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.contMDiff.comp hf

private theorem contMDiff_horosphericalPoint :
    ContMDiff 𝓘(ℝ, E₃) 𝓘(ℝ, E₃) ∞ horosphericalPoint := by
  have hc (i : Fin 3) : ContMDiff 𝓘(ℝ, E₃) 𝓘(ℝ, ℝ) ∞
      (fun u : U => u.val i) :=
    (contDiff_euclideanCoordinate i).contMDiff.comp contMDiff_subtype_val
  have hf : ContMDiff 𝓘(ℝ, E₃) 𝓘(ℝ, Fin 3 → ℝ) ∞
      (fun u : U => ![-u.val 0 / 2 + 1 / (2 * u.val 0) +
        u.val 0 * ((u.val 1) ^ 2 + (u.val 2) ^ 2) / 8,
        u.val 0 / 2 * u.val 1, u.val 0 / 2 * u.val 2]) := by
    apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · exact (((hc 0).neg.div_const 2).add
        (contMDiff_const.div₀ (contMDiff_const.mul (hc 0))
          (fun u => mul_ne_zero (by norm_num) u.property.ne'))).add
        (((hc 0).mul (((hc 1).pow 2).add ((hc 2).pow 2))).div_const 8)
    · exact ((hc 0).div_const 2).mul (hc 1)
    · exact ((hc 0).div_const 2).mul (hc 2)
  have hg := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.contMDiff.comp hf
  have he : horosphericalPoint = ofSpace ∘
      (fun u : U => WithLp.toLp 2 ![-u.val 0 / 2 + 1 / (2 * u.val 0) +
        u.val 0 * ((u.val 1) ^ 2 + (u.val 2) ^ 2) / 8,
        u.val 0 / 2 * u.val 1, u.val 0 / 2 * u.val 2]) := by
    funext u
    apply Hyperboloid.ext
    have hs := congrArg Prod.snd (northPoleHorosphereHomeomorph_symm_coordinates
      (u.val 0) u.property ((u.val 1 : ℂ) + (u.val 2 : ℂ) * Complex.I))
    dsimp only at hs
    change (horosphericalPoint u).space = _
    dsimp only [horosphericalPoint]
    rw [hs]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [pow_two]
  rw [he]
  exact contMDiff_ofSpace.comp hg

def horosphericalDiffeomorph : Hyperboloid E₃ ≃ₘ⟮𝓘(ℝ, E₃), 𝓘(ℝ, E₃)⟯ U where
  toFun := horosphericalCoordinate
  invFun := horosphericalPoint
  left_inv := horosphericalPoint_coordinate
  right_inv := horosphericalCoordinate_point
  contMDiff_toFun := contMDiff_horosphericalCoordinate
  contMDiff_invFun := contMDiff_horosphericalPoint

theorem horosphericalDiffeomorph_apply (x : Hyperboloid E₃) :
    (horosphericalDiffeomorph x).val = WithLp.toLp 2 ![x.time - x.space 0,
      2 * x.space 1 / (x.time - x.space 0), 2 * x.space 2 / (x.time - x.space 0)] := rfl

theorem horosphericalDiffeomorph_symm_apply (u : U) :
    horosphericalDiffeomorph.symm u =
      ((northPoleHorosphereHomeomorph (u.val 0) u.property).symm
        ((u.val 1 : ℂ) + (u.val 2 : ℂ) * Complex.I)).val := rfl

end DifferentialGeometry.Hyperboloid
