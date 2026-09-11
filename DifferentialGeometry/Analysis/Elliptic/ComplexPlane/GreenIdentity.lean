import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.PolarDivergence
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.CompCLM



noncomputable section

open Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis


theorem laplacian_complex_eq_fderiv (f : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian f z =
      fderiv ℝ (fderiv ℝ f) z 1 1 +
      fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I := by
  simp [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply]

private theorem fderiv_partial {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (v w : ℂ) :
    fderiv ℝ (fun q => fderiv ℝ f q v) z w =
      fderiv ℝ (fderiv ℝ f) z w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp


theorem complexDivergence_gradient {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) :
    complexDivergence (fun q => fderiv ℝ f q 1)
      (fun q => fderiv ℝ f q Complex.I) z = Laplacian.laplacian f z := by
  rw [complexDivergence, fderiv_partial hf, fderiv_partial hf,
    laplacian_complex_eq_fderiv]


theorem complexDivergence_green {u v : ℂ → ℝ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (hv : ContDiffAt ℝ 2 v z) :
    complexDivergence
      (fun q => u q * fderiv ℝ v q 1 - v q * fderiv ℝ u q 1)
      (fun q => u q * fderiv ℝ v q Complex.I - v q * fderiv ℝ u q Complex.I) z =
      u z * Laplacian.laplacian v z - v z * Laplacian.laplacian u z := by
  have hu₁ := hu.differentiableAt (by norm_num)
  have hv₁ := hv.differentiableAt (by norm_num)
  have hdu (e : ℂ) : DifferentiableAt ℝ (fun q => fderiv ℝ u q e) z :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hdv (e : ℂ) : DifferentiableAt ℝ (fun q => fderiv ℝ v q e) z :=
    ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  unfold complexDivergence
  erw [fderiv_fun_sub (hu₁.mul (hdv 1)) (hv₁.mul (hdu 1)),
    fderiv_fun_sub (hu₁.mul (hdv Complex.I)) (hv₁.mul (hdu Complex.I)),
    fderiv_fun_mul hu₁ (hdv 1), fderiv_fun_mul hv₁ (hdu 1),
    fderiv_fun_mul hu₁ (hdv Complex.I), fderiv_fun_mul hv₁ (hdu Complex.I)]
  simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
    fderiv_partial hu, fderiv_partial hv, laplacian_complex_eq_fderiv]
  ring


theorem apply_polar_unit (L : ℂ →L[ℝ] ℝ) (θ : ℝ) :
    L (Complex.polarCoord.symm (1, θ)) = Real.cos θ * L 1 + Real.sin θ * L Complex.I := by
  have h : Complex.polarCoord.symm (1, θ) =
      Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
    simp [Complex.polarCoord_symm_apply, Complex.real_smul]
  rw [h, map_add, map_smul, map_smul]
  rfl


def greenRadialFlux (u v : ℂ → ℝ) (r θ : ℝ) : ℝ :=
  let z := Complex.polarCoord.symm (r, θ)
  let e := Complex.polarCoord.symm (1, θ)
  r * (u z * fderiv ℝ v z e - v z * fderiv ℝ u z e)




theorem integral_green_annulus {u v : ℂ → ℝ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hu : ∀ z, ‖z‖ ∈ Icc r R → ContDiffAt ℝ 2 u z)
    (hv : ∀ z, ‖z‖ ∈ Icc r R → ContDiffAt ℝ 2 v z) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R},
      u z * Laplacian.laplacian v z - v z * Laplacian.laplacian u z) =
      (∫ θ in -Real.pi..Real.pi, greenRadialFlux u v R θ) -
        ∫ θ in -Real.pi..Real.pi, greenRadialFlux u v r θ := by
  let F := fun z => u z * fderiv ℝ v z 1 - v z * fderiv ℝ u z 1
  let G := fun z => u z * fderiv ℝ v z Complex.I - v z * fderiv ℝ u z Complex.I
  have hreg (e : ℂ) (z : ℂ) (hz : ‖z‖ ∈ Icc r R) :
      ContDiffAt ℝ 1 (fun q => u q * fderiv ℝ v q e - v q * fderiv ℝ u q e) z := by
    exact ((hu z hz |>.of_le (by norm_num)).mul
      (((hv z hz).fderiv_right (by norm_num)).clm_apply contDiffAt_const)).sub
      ((hv z hz |>.of_le (by norm_num)).mul
        (((hu z hz).fderiv_right (by norm_num)).clm_apply contDiffAt_const))
  have h := integral_complexDivergence_annulus hr hrR (hreg 1) (hreg Complex.I)
  have hflux (a θ : ℝ) :
      a * (F (Complex.polarCoord.symm (a, θ)) * Real.cos θ +
        G (Complex.polarCoord.symm (a, θ)) * Real.sin θ) = greenRadialFlux u v a θ := by
    simp only [greenRadialFlux, apply_polar_unit, F, G]
    ring
  change (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, complexDivergence F G z) = _ at h
  dsimp only [F, G] at hflux
  simp_rw [hflux] at h
  rw [← h]
  apply setIntegral_congr_fun (measurableSet_Icc.preimage continuous_norm.measurable)
  intro z hz
  exact (complexDivergence_green (hu z hz) (hv z hz)).symm

end DifferentialGeometry.Analysis
