import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic

private theorem tsupport_tensor_mul_subset {E : Type*} [TopologicalSpace E]
    {τ : ℝ → ℝ} {ψ : E → ℝ} :
    tsupport (fun p : ℝ × E => τ p.1 * ψ p.2) ⊆ tsupport τ ×ˢ tsupport ψ := by
  apply closure_minimal
  · intro p hp
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hp
    exact ⟨subset_tsupport τ hp.1, subset_tsupport ψ hp.2⟩
  · exact (isClosed_tsupport τ).prod (isClosed_tsupport ψ)

private theorem hasCompactSupport_tensor_mul {E : Type*} [TopologicalSpace E]
    {τ : ℝ → ℝ} {ψ : E → ℝ}
    (hτ : HasCompactSupport τ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun p : ℝ × E => τ p.1 * ψ p.2) :=
  (hτ.isCompact.prod hψ.isCompact).of_isClosed_subset (isClosed_tsupport _)
    tsupport_tensor_mul_subset

private theorem fderiv_tensor_mul_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {τ : ℝ → ℝ} {ψ : E → ℝ}
    (hτ : Differentiable ℝ τ) (hψ : Differentiable ℝ ψ) (p : ℝ × E) :
    fderiv ℝ (fun p : ℝ × E => τ p.1 * ψ p.2) p (1, 0) =
      deriv τ p.1 * ψ p.2 := by
  have hτp : DifferentiableAt ℝ (fun p : ℝ × E => τ p.1) p := hτ.differentiableAt.comp p differentiableAt_fst
  have hψp : DifferentiableAt ℝ (fun p : ℝ × E => ψ p.2) p := hψ.differentiableAt.comp p differentiableAt_snd
  rw [fderiv_fun_mul hτp hψp]
  change τ p.1 * (fderiv ℝ (ψ ∘ Prod.snd) p) (1, 0) +
    ψ p.2 * (fderiv ℝ (τ ∘ Prod.fst) p) (1, 0) = _
  rw [fderiv_comp p hψ.differentiableAt differentiableAt_snd,
    fderiv_comp p hτ.differentiableAt differentiableAt_fst]
  rw [fderiv_snd, fderiv_fst]
  change τ p.1 * fderiv ℝ ψ p.2 0 + ψ p.2 * fderiv ℝ τ p.1 1 = _
  simp only [map_zero, mul_zero, zero_add]
  rw [fderiv_apply_one_eq_deriv]
  exact mul_comm _ _

private theorem fderiv_tensor_cutoff_div_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {τ : ℝ → ℝ} {η ψ : E → ℝ}
    {r : ℝ × E → ℝ}
    (hτ : Differentiable ℝ τ) (hη : Differentiable ℝ η)
    (p : ℝ × E) (hψ : DifferentiableAt ℝ ψ p.2)
    (hr : DifferentiableAt ℝ r p) (hrne : r p ≠ 0) (v : E) :
    fderiv ℝ (fun z => τ z.1 * (η z.2 * ψ z.2) / r z) p
        (0, v) =
      τ p.1 * ((η p.2 / r p) * fderiv ℝ ψ p.2 v +
        fderiv ℝ (fun z => η z.2 / r z) p (0, v) * ψ p.2) := by
  let f := fun z : ℝ × E => η z.2 / r z
  have hηp : DifferentiableAt ℝ (fun z : ℝ × E => η z.2) p :=
    (hη p.2).comp p differentiableAt_snd
  have hf : DifferentiableAt ℝ f p := by
    change DifferentiableAt ℝ (fun z => η z.2 * (r z)⁻¹) p
    exact hηp.mul (hr.inv hrne)
  have hψp : DifferentiableAt ℝ (fun z : ℝ × E => ψ z.2) p :=
    hψ.comp p differentiableAt_snd
  have hτp : DifferentiableAt ℝ (fun z : ℝ × E => τ z.1) p :=
    (hτ p.1).comp p differentiableAt_fst
  have heq : (fun z => τ z.1 * (η z.2 * ψ z.2) / r z) =
      fun z => τ z.1 * (f z * ψ z.2) := by
    funext z
    dsimp [f]
    ring
  rw [heq]
  have hfψ : DifferentiableAt ℝ (fun z => f z * ψ z.2) p := hf.mul hψp
  rw [fderiv_fun_mul hτp hfψ, fderiv_fun_mul hf hψp]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have hdψ : fderiv ℝ (fun z : ℝ × E => ψ z.2) p
      (0, v) = fderiv ℝ ψ p.2 v := by
    change fderiv ℝ (ψ ∘ Prod.snd) p _ = _
    rw [fderiv_comp p hψ differentiableAt_snd, fderiv_snd]
    rfl
  have hdτ : fderiv ℝ (fun z : ℝ × E => τ z.1) p
      (0, v) = 0 := by
    change fderiv ℝ (τ ∘ Prod.fst) p _ = _
    rw [fderiv_comp p (hτ p.1) differentiableAt_fst, fderiv_fst]
    exact map_zero (fderiv ℝ τ p.1)
  rw [hdψ, hdτ]
  simp only [mul_zero, add_zero]
  ring

theorem integral_fixed_density_tensor_test
    {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [Fintype J] (v : J → E) {Ω : Set E} {a b : ℝ}
    (hΩ : IsOpen Ω) {ν : Measure (ℝ × E)}
    {r W C : ℝ × E → ℝ}
    {P : J → ℝ × E → ℝ}
    {η ψ : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ Ω)
    (hgood : ∀ᵐ p ∂ν, DifferentiableAt ℝ ψ p.2 ∧ DifferentiableAt ℝ r p ∧ r p ≠ 0)
    (hweak : ∀ φ : ℝ × E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, W p * fderiv ℝ φ p (1, 0) ∂ν) =
        (∑ j, ∫ p, P j p * fderiv ℝ (fun z => φ z / r z) p
          (0, v j) ∂ν) - ∫ p, C p * φ p ∂ν)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ (⊤ : ℕ∞) τ) (hτc : HasCompactSupport τ)
    (hτs : tsupport τ ⊆ Ioo a b)
    (hmain : ∀ j, Integrable (fun p => τ p.1 * ((η p.2 / r p) * P j p) *
      fderiv ℝ ψ p.2 (v j)) ν)
    (herr : ∀ j, Integrable (fun p => τ p.1 * (P j p *
      fderiv ℝ (fun z => η z.2 / r z) p (0, v j)) * ψ p.2) ν)
    (hsource : Integrable (fun p => τ p.1 * (η p.2 * C p) * ψ p.2) ν) :
    (∫ p, deriv τ p.1 * (η p.2 * W p) * ψ p.2 ∂ν) =
      (∑ j, ∫ p, τ p.1 * ((η p.2 / r p) * P j p) *
        fderiv ℝ ψ p.2 (v j) ∂ν) -
      ∫ p, τ p.1 * (η p.2 * C p - ∑ j, P j p *
        fderiv ℝ (fun z => η z.2 / r z) p (0, v j)) * ψ p.2 ∂ν := by
  classical
  have hηψs : tsupport (fun z => η z * ψ z) ⊆ Ω := tsupport_mul_subset_left.trans hηs
  have hηψ : ContDiff ℝ (⊤ : ℕ∞) (fun z => η z * ψ z) :=
    (hη.contDiffOn.mul hψ).contDiff_of_tsupport_subset hΩ hηψs
  have hφ := hweak (fun p => τ p.1 * (η p.2 * ψ p.2))
    ((hτ.comp contDiff_fst).mul (hηψ.comp contDiff_snd))
    (hasCompactSupport_tensor_mul hτc hηc.mul_right)
    (tsupport_tensor_mul_subset.trans (Set.prod_mono hτs hηψs))
  have hl : (∫ p, W p * fderiv ℝ (fun p => τ p.1 * (η p.2 * ψ p.2)) p (1, 0) ∂ν) =
      ∫ p, deriv τ p.1 * (η p.2 * W p) * ψ p.2 ∂ν := by
    apply integral_congr_ae
    filter_upwards with p
    rw [fderiv_tensor_mul_time (hτ.differentiable (by simp)) (hηψ.differentiable (by simp))]
    ring
  have hs : (∫ p, C p * (τ p.1 * (η p.2 * ψ p.2)) ∂ν) =
      ∫ p, τ p.1 * (η p.2 * C p) * ψ p.2 ∂ν := by
    apply integral_congr_ae
    filter_upwards with p
    ring
  have hj (j) : (∫ p, P j p * fderiv ℝ (fun z => τ z.1 * (η z.2 * ψ z.2) / r z) p
      (0, v j) ∂ν) =
      (∫ p, τ p.1 * ((η p.2 / r p) * P j p) *
        fderiv ℝ ψ p.2 (v j) ∂ν) +
      ∫ p, τ p.1 * (P j p *
        fderiv ℝ (fun z => η z.2 / r z) p (0, v j)) * ψ p.2 ∂ν := by
    rw [← integral_add (hmain j) (herr j)]
    apply integral_congr_ae
    filter_upwards [hgood] with p hp
    rw [fderiv_tensor_cutoff_div_space (hτ.differentiable (by simp))
      (hη.differentiable (by simp)) p hp.1 hp.2.1 hp.2.2 (v j)]
    ring
  have hb : (∫ p, τ p.1 * (η p.2 * C p - ∑ j, P j p *
        fderiv ℝ (fun z => η z.2 / r z) p (0, v j)) * ψ p.2 ∂ν) =
      (∫ p, τ p.1 * (η p.2 * C p) * ψ p.2 ∂ν) -
        ∑ j, ∫ p, τ p.1 * (P j p *
          fderiv ℝ (fun z => η z.2 / r z) p (0, v j)) * ψ p.2 ∂ν := by
    simp_rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    rw [integral_sub hsource (integrable_finsetSum _ (fun j _ => herr j)),
      integral_finsetSum _ (fun j _ => herr j)]
  rw [hl, hs] at hφ
  simp_rw [hj, Finset.sum_add_distrib] at hφ
  rw [hb]
  linarith only [hφ]

end DifferentialGeometry.Analysis.Parabolic
