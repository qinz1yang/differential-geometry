import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {μ : Measure E} {Ω : Set E}

omit [MeasurableSpace E] in
private theorem fderiv_fderiv_apply_comm
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
      fderiv ℝ (fun y => fderiv ℝ φ y w) x v := by
  have hc : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_cast)
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x := (hc.differentiable (by norm_num)) x
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  rw [fderiv_fun_const, fderiv_fun_const]
  simp only [add_apply, ContinuousLinearMap.comp_apply, Pi.zero_apply, zero_apply, map_zero, zero_add]
  exact hφ.contDiffAt.isSymmSndFDerivAt (by simpa only [minSmoothness_of_isRCLikeNormedField] using (show (2 : ℕ∞ω) ≤ (⊤ : ℕ∞) from by norm_cast)) w v

theorem integral_weak_deriv_fderiv_comm
    {U V R : E → ℝ} (v w : E)
    (hv : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, V x * φ x ∂μ)
    (hw : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ x, U x * fderiv ℝ φ x w ∂μ) = -∫ x, R x * φ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) :
    (∫ x, V x * fderiv ℝ φ x w ∂μ) = ∫ x, R x * fderiv ℝ φ x v ∂μ := by
  have hd (z : E) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ φ x z) :=
    (hφ.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have h₁ := hv (fun x => fderiv ℝ φ x w) (hd w) (hφc.fderiv_apply ℝ w)
    ((tsupport_fderiv_apply_subset ℝ w).trans hφs)
  have h₂ := hw (fun x => fderiv ℝ φ x v) (hd v) (hφc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hφs)
  apply neg_injective
  rw [← h₁, ← h₂]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [fderiv_fderiv_apply_comm hφ x w v]

end DifferentialGeometry.Analysis.Sobolev
