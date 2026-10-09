import DifferentialGeometry.Analysis.Elliptic.Planar.CoordinateChange
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Analysis

/-- Precomposing the supplied principal chart by the inverse dilation gives a
chart for the original coefficient. The two-dimensional determinant and the
bilinear principal expression acquire the same positive factor. -/
theorem rescale_principal_chart
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hzero : (0 : ℂ) ∈ e.source) (hsource : e.source ⊆ ball 0 R)
    (hezero : e 0 = 0)
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hdet : ∀ z ∈ e.source, 0 < (fderiv ℝ e z).det)
    (hprincipal : ∀ z ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
      (∑ i : Fin 2, ∑ j : Fin 2, A (ρ • z) i j *
        H (fderiv ℝ e z ((![1, Complex.I] : Fin 2 → ℂ) i))
          (fderiv ℝ e z ((![1, Complex.I] : Fin 2 → ℂ) j))) =
        (fderiv ℝ e z).det * (H 1 1 + H Complex.I Complex.I)) :
    let f : OpenPartialHomeomorph ℂ ℂ :=
      (Homeomorph.smulOfNeZero ρ⁻¹ (inv_ne_zero hρ.ne')).toOpenPartialHomeomorph.trans e
    (∀ z, f z = e (ρ⁻¹ • z)) ∧
      (∀ y, f.symm y = ρ • e.symm y) ∧
      f.source = (fun z : ℂ => ρ⁻¹ • z) ⁻¹' e.source ∧
      f.target = e.target ∧
      0 < ρ * R ∧ (0 : ℂ) ∈ f.source ∧ f.source ⊆ ball 0 (ρ * R) ∧ f 0 = 0 ∧
      ContDiffOn ℝ 1 f f.source ∧ ContDiffOn ℝ 1 f.symm f.target ∧
      (∀ z ∈ f.source, fderiv ℝ f z = ρ⁻¹ • fderiv ℝ e (ρ⁻¹ • z)) ∧
      (∀ z ∈ f.source, (fderiv ℝ f z).det =
        (ρ⁻¹) ^ 2 * (fderiv ℝ e (ρ⁻¹ • z)).det) ∧
      (∀ z ∈ f.source, 0 < (fderiv ℝ f z).det) ∧
      (∀ z ∈ f.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
        (∑ i : Fin 2, ∑ j : Fin 2, A z i j *
          H (fderiv ℝ f z ((![1, Complex.I] : Fin 2 → ℂ) i))
            (fderiv ℝ f z ((![1, Complex.I] : Fin 2 → ℂ) j))) =
          (fderiv ℝ f z).det * (H 1 1 + H Complex.I Complex.I)) := by
  intro f
  have hf_apply (z : ℂ) : f z = e (ρ⁻¹ • z) := rfl
  have hf_symm (y : ℂ) : f.symm y = ρ • e.symm y := by
    change (ρ⁻¹)⁻¹ • e.symm y = ρ • e.symm y
    rw [inv_inv]
  have hfs : f.source = (fun z : ℂ => ρ⁻¹ • z) ⁻¹' e.source := by
    change univ ∩ (fun z : ℂ => ρ⁻¹ • z) ⁻¹' e.source = _
    exact univ_inter _
  have hft : f.target = e.target := by
    change e.target ∩ e.symm ⁻¹' univ = e.target
    rw [preimage_univ, inter_univ]
  have hmap : MapsTo (fun z : ℂ => ρ⁻¹ • z) f.source e.source := by
    intro z hz
    rwa [hfs] at hz
  have hfc : ContDiffOn ℝ 1 f f.source := by
    change ContDiffOn ℝ 1 (fun z => e (ρ⁻¹ • z)) f.source
    have hs : ContDiff ℝ 1 (fun z : ℂ => ρ⁻¹ • z) :=
      (contDiff_id : ContDiff ℝ 1 (fun z : ℂ => z)).const_smul ρ⁻¹
    exact he.comp hs.contDiffOn hmap
  have hfic : ContDiffOn ℝ 1 f.symm f.target := by
    change ContDiffOn ℝ 1 (fun y => (ρ⁻¹)⁻¹ • e.symm y) f.target
    rw [inv_inv, hft]
    exact hei.const_smul ρ
  have hfd (z : ℂ) (hz : z ∈ f.source) :
      fderiv ℝ f z = ρ⁻¹ • fderiv ℝ e (ρ⁻¹ • z) := by
    have hed : DifferentiableAt ℝ e (ρ⁻¹ • z) :=
      (he.contDiffAt (e.open_source.mem_nhds (hmap hz))).differentiableAt one_ne_zero
    have hscale : HasFDerivAt (fun x : ℂ => ρ⁻¹ • x)
        (ρ⁻¹ • ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id z).const_smul ρ⁻¹
    change fderiv ℝ (fun x => e (ρ⁻¹ • x)) z = _
    have hd : fderiv ℝ (fun x : ℂ => e (ρ⁻¹ • x)) z =
        (fderiv ℝ e (ρ⁻¹ • z)).comp (ρ⁻¹ • ContinuousLinearMap.id ℝ ℂ) :=
      (hed.hasFDerivAt.comp z hscale).fderiv
    rw [hd]
    ext v
    change fderiv ℝ e (ρ⁻¹ • z) (ρ⁻¹ • v) =
      ρ⁻¹ • fderiv ℝ e (ρ⁻¹ • z) v
    exact map_smul _ _ _
  have hfj (z : ℂ) (hz : z ∈ f.source) :
      (fderiv ℝ f z).det = (ρ⁻¹) ^ 2 * (fderiv ℝ e (ρ⁻¹ • z)).det := by
    rw [hfd z hz]
    change LinearMap.det (ρ⁻¹ • (fderiv ℝ e (ρ⁻¹ • z)).toLinearMap) = _
    rw [LinearMap.det_smul, Complex.finrank_real_complex]
  refine ⟨hf_apply, hf_symm, hfs, hft, mul_pos hρ hR, ?_, ?_, ?_,
    hfc, hfic, hfd, hfj, ?_, ?_⟩
  · rw [hfs]
    change ρ⁻¹ • (0 : ℂ) ∈ e.source
    simpa only [smul_zero] using hzero
  · intro z hz
    have hzR : ‖ρ⁻¹ • z‖ < R := by
      simpa only [mem_ball, dist_zero_right] using hsource (hmap hz)
    have hn : ρ * ‖ρ⁻¹ • z‖ = ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ),
        ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
    rw [mem_ball, dist_zero_right, ← hn]
    exact mul_lt_mul_of_pos_left hzR hρ
  · rw [hf_apply, smul_zero, hezero]
  · intro z hz
    rw [hfj z hz]
    exact mul_pos (pow_pos (inv_pos.mpr hρ) 2) (hdet _ (hmap hz))
  · intro z hz H
    have hp := hprincipal (ρ⁻¹ • z) (hmap hz) H
    simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul] at hp
    rw [hfj z hz]
    simp only [hfd z hz, smul_apply, map_smul, smul_eq_mul]
    calc
      _ = (ρ⁻¹) ^ 2 *
          (∑ i : Fin 2, ∑ j : Fin 2, A z i j *
            H (fderiv ℝ e (ρ⁻¹ • z) ((![1, Complex.I] : Fin 2 → ℂ) i))
              (fderiv ℝ e (ρ⁻¹ • z) ((![1, Complex.I] : Fin 2 → ℂ) j))) := by
        simp only [Fin.sum_univ_two]
        ring
      _ = (ρ⁻¹) ^ 2 *
          ((fderiv ℝ e (ρ⁻¹ • z)).det * (H 1 1 + H Complex.I Complex.I)) := by rw [hp]
      _ = _ := by ring

end DifferentialGeometry.Analysis
