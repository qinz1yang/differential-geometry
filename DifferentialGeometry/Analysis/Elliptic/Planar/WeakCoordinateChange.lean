import DifferentialGeometry.Analysis.Elliptic.Planar.CoordinateChange
import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem exists_compact_contDiff_test_pullback
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : ContDiffOn ℝ 1 e e.source)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ e.target) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ e.source ∧ EqOn ψ (fun x => φ (e x)) e.source := by
  classical
  let ψ : ℂ → ℝ := e.source.indicator (fun x => φ (e x))
  let K : Set ℂ := e.symm '' tsupport φ
  have hK : IsCompact K := hφc.image_of_continuousOn (e.continuousOn_symm.mono hφs)
  have hKs : K ⊆ e.source := by
    rintro x ⟨y, hy, rfl⟩
    exact e.map_target (hφs hy)
  have hsupp : Function.support ψ ⊆ K := by
    intro x hx
    change ψ x ≠ 0 at hx
    have hxs : x ∈ e.source := by
      by_contra hh
      exact hx (by simp [ψ, hh])
    have hvalue : φ (e x) ≠ 0 := by simpa only [ψ, indicator_of_mem hxs] using hx
    exact ⟨e x, subset_tsupport φ hvalue, e.left_inv hxs⟩
  have hts : tsupport ψ ⊆ K := closure_minimal hsupp hK.isClosed
  have heq : EqOn ψ (fun x => φ (e x)) e.source := by
    intro x hx
    exact indicator_of_mem hx _
  have hψ : ContDiffOn ℝ 1 ψ e.source :=
    (hφ.comp_contDiffOn he).congr heq
  exact ⟨ψ, hψ.contDiff_of_tsupport_subset e.open_source (hts.trans hKs),
    hK.of_isClosed_subset (isClosed_tsupport ψ) hts, hts.trans hKs, heq⟩

/-- A determinant-normalized C1 coordinate map carries the weak divergence
identity to the weak scalar Laplacian. The drift uses only the first coordinate
derivative. The transported scalar is literally the supplied scalar composed
with the inverse of this same chart. -/
theorem planar_weak_divergence_pushforward
    (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (d : ℂ → Fin 2 → ℝ) (c w : ℂ → ℝ)
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hw : ContDiffOn ℝ 1 w e.source)
    (he : ContDiffOn ℝ 1 e e.source)
    (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hdet : ∀ x ∈ e.source, 0 < (fderiv ℝ e x).det)
    (hprincipal : ∀ x ∈ e.source, ∀ H : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
      (∑ i : Fin 2, ∑ j : Fin 2, A x i j *
        H (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) i))
          (fderiv ℝ e x ((![1, Complex.I] : Fin 2 → ℂ) j))) =
        (fderiv ℝ e x).det * (H 1 1 + H Complex.I Complex.I))
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ e.source →
      (∫ x in e.source, ∑ i : Fin 2, ∑ j : Fin 2, A x i j *
        fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j) *
        fderiv ℝ ψ x ((![1, Complex.I] : Fin 2 → ℂ) i)) =
      ∫ x in e.source, ((∑ j : Fin 2, d x j *
        fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j)) + c x * w x) * ψ x) :
    let v : ℂ → ℝ := fun y => w (e.symm y)
    let b : ℂ → ℂ := fun y => ((fderiv ℝ e (e.symm y)).det)⁻¹ •
      (∑ j : Fin 2, d (e.symm y) j •
        fderiv ℝ e (e.symm y) ((![1, Complex.I] : Fin 2 → ℂ) j))
    let q : ℂ → ℝ := fun y => c (e.symm y) / (fderiv ℝ e (e.symm y)).det
    ContDiffOn ℝ 1 v e.target ∧
      (∀ x ∈ e.source, v (e x) = w x) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ e.target →
        (∫ y in e.target, fderiv ℝ v y 1 * fderiv ℝ φ y 1 +
          fderiv ℝ v y Complex.I * fderiv ℝ φ y Complex.I) =
        ∫ y in e.target, (fderiv ℝ v y (b y) + q y * v y) * φ y := by
  intro v b q
  have hv : ContDiffOn ℝ 1 v e.target :=
    hw.comp hei (fun y hy => e.map_target hy)
  have hvw : ∀ x ∈ e.source, v (e x) = w x := by
    intro x hx
    exact congrArg w (e.left_inv hx)
  refine ⟨hv, hvw, ?_⟩
  intro φ hφ hφc hφs
  obtain ⟨ψ, hψ, hψc, hψs, hψeq⟩ :=
    exists_compact_contDiff_test_pullback e he hφ hφc hφs
  have hderiv (x : ℂ) (hx : x ∈ e.source) :
      fderiv ℝ w x = (fderiv ℝ v (e x)).comp (fderiv ℝ e x) := by
    have heq : w =ᶠ[𝓝 x] fun z => v (e z) := by
      filter_upwards [e.open_source.mem_nhds hx] with z hz
      exact (hvw z hz).symm
    rw [heq.fderiv_eq]
    exact fderiv_fun_comp x
      ((hv.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt one_ne_zero)
      ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt one_ne_zero)
  have htest (x : ℂ) (hx : x ∈ e.source) :
      fderiv ℝ ψ x = (fderiv ℝ φ (e x)).comp (fderiv ℝ e x) := by
    have heq : ψ =ᶠ[𝓝 x] fun z => φ (e z) := by
      filter_upwards [e.open_source.mem_nhds hx] with z hz
      exact hψeq hz
    rw [heq.fderiv_eq]
    exact fderiv_fun_comp x (hφ.differentiable one_ne_zero (e x))
      ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt one_ne_zero)
  have hleft (x : ℂ) (hx : x ∈ e.source) :
      (∑ i : Fin 2, ∑ j : Fin 2, A x i j *
        fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j) *
        fderiv ℝ ψ x ((![1, Complex.I] : Fin 2 → ℂ) i)) =
      (fderiv ℝ e x).det *
        (fderiv ℝ v (e x) 1 * fderiv ℝ φ (e x) 1 +
          fderiv ℝ v (e x) Complex.I * fderiv ℝ φ (e x) Complex.I) := by
    have hp := hprincipal x hx
      ((fderiv ℝ φ (e x)).smulRight (fderiv ℝ v (e x)))
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul] at hp
    rw [hderiv x hx, htest x hx]
    simp only [ContinuousLinearMap.comp_apply]
    simp only [Fin.sum_univ_two] at hp ⊢
    convert hp using 1 <;> ring
  have hright (x : ℂ) (hx : x ∈ e.source) :
      ((∑ j : Fin 2, d x j * fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j)) +
        c x * w x) * ψ x =
      (fderiv ℝ e x).det *
        ((fderiv ℝ v (e x) (b (e x)) + q (e x) * v (e x)) * φ (e x)) := by
    rw [hψeq hx, ← hvw x hx, hderiv x hx]
    simp only [b, q, e.left_inv hx, map_smul, map_sum,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    field_simp [(hdet x hx).ne']
  have hederiv : ∀ x ∈ e.source, HasFDerivAt e (fderiv ℝ e x) x := by
    intro x hx
    exact ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt
  have hsource := hweak ψ hψ hψc hψs
  rw [integral_target_eq_integral_abs_det_fderiv_smul volume hederiv,
    integral_target_eq_integral_abs_det_fderiv_smul volume hederiv]
  calc
    _ = ∫ x in e.source, ∑ i : Fin 2, ∑ j : Fin 2, A x i j *
        fderiv ℝ w x ((![1, Complex.I] : Fin 2 → ℂ) j) *
        fderiv ℝ ψ x ((![1, Complex.I] : Fin 2 → ℂ) i) := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro x hx
      simpa only [abs_of_pos (hdet x hx), smul_eq_mul] using (hleft x hx).symm
    _ = _ := hsource
    _ = _ := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro x hx
      simpa only [abs_of_pos (hdet x hx), smul_eq_mul] using hright x hx

end DifferentialGeometry.Analysis
