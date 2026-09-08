import DifferentialGeometry.Analysis.Calculus.ContDiff.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open Filter MeasureTheory Set

namespace DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

theorem integral_fderiv_eq_neg_of_weighted_identity
    {μ : Measure E} {S : Set E} (hS : IsOpen S)
    {U R ρ : E → ℝ} (v : E)
    (hU : LocallyIntegrable U μ) (hR : LocallyIntegrable R μ)
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ S) (hρne : ∀ x ∈ S, ρ x ≠ 0)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → (∫ x, ρ x * U x * fderiv ℝ φ x v ∂μ) = -∫ x, R x * φ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ S) :
    (∫ x, U x * fderiv ℝ φ x v ∂μ) =
      -∫ x, ((ρ x)⁻¹ * R x - ((ρ x)⁻¹ * fderiv ℝ ρ x v) * U x) * φ x ∂μ := by
  let ψ := fun x => φ x / ρ x
  have hψs : tsupport ψ ⊆ S := by
    simpa only [ψ, div_eq_mul_inv] using
      (tsupport_mul_subset_left (f := φ) (g := fun x => (ρ x)⁻¹)).trans hφs
  have hψc : HasCompactSupport ψ := by
    exact hφc.of_isClosed_subset (isClosed_tsupport ψ) (by
      simpa only [ψ, div_eq_mul_inv] using
        (tsupport_mul_subset_left (f := φ) (g := fun x => (ρ x)⁻¹)))
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (hφ.contDiffOn.div hρ hρne).contDiff_of_tsupport_subset hS hψs
  have hD (x) (hx : x ∈ S) : fderiv ℝ ψ x v =
      fderiv ℝ φ x v / ρ x - φ x * fderiv ℝ ρ x v / (ρ x)^2 := by
    have hDρx := (hρ.differentiableOn (by simp) x hx).differentiableAt (hS.mem_nhds hx)
    have hi := (hasFDerivAt_inv (hρne x hx)).comp x hDρx.hasFDerivAt
    have hd := (hφ.differentiable (by simp) x).hasFDerivAt.mul hi
    change fderiv ℝ (fun x => φ x / ρ x) x v = _
    simp only [div_eq_mul_inv]
    change fderiv ℝ (φ * ((fun x : ℝ => x⁻¹) ∘ ρ)) x v = _
    rw [hd.fderiv]
    simp only [add_apply, smul_apply, Function.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    field_simp [hρne x hx]
    ring
  have heq : (fun x => ρ x * U x * fderiv ℝ ψ x v) =ᵐ[μ] fun x =>
      U x * fderiv ℝ φ x v - ((ρ x)⁻¹ * fderiv ℝ ρ x v) * U x * φ x := by
    filter_upwards [] with x
    by_cases hx : x ∈ S
    · rw [hD x hx]
      field_simp [hρne x hx]
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
      have hdφx : fderiv ℝ φ x v = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ φ y v)
        (fun h => hx (hφs (tsupport_fderiv_apply_subset ℝ v h)))
      have hdψx : fderiv ℝ ψ x v = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ ψ y v)
        (fun h => hx (hψs (tsupport_fderiv_apply_subset ℝ v h)))
      simp only [hφx, hdφx, hdψx, mul_zero, sub_zero]
  have ht := hweak ψ hψ hψc hψs
  let θ := fun x => ((ρ x)⁻¹ * fderiv ℝ ρ x v) * φ x
  have hθsupp : tsupport θ ⊆ tsupport φ := tsupport_mul_subset_right
  have hθc : HasCompactSupport θ :=
    hφc.of_isClosed_subset (isClosed_tsupport θ) hθsupp
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := by
    have hDρ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ρ x v) S :=
      (hρ.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
    exact (((hρ.inv hρne).mul hDρ).mul hφ.contDiffOn).contDiff_of_tsupport_subset hS
      (hθsupp.trans hφs)
  have hI : Integrable (fun x => U x * fderiv ℝ φ x v) μ :=
    hU.integrable_smul_right_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply (𝕜 := ℝ) v)
  have hJ : Integrable (fun x => ((ρ x)⁻¹ * fderiv ℝ ρ x v) * U x * φ x) μ := by
    convert hU.integrable_smul_right_of_hasCompactSupport hθ.continuous hθc using 1
    ext x
    dsimp [θ]
    ring
  have hK : Integrable (fun x => (ρ x)⁻¹ * R x * φ x) μ := by
    convert hR.integrable_smul_right_of_hasCompactSupport hψ.continuous hψc using 1
    ext x
    dsimp [ψ]
    ring
  rw [integral_congr_ae heq, integral_sub hI hJ] at ht
  have hr : (∫ x, R x * ψ x ∂μ) = ∫ x, (ρ x)⁻¹ * R x * φ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [ψ]
    ring
  rw [hr] at ht
  have hc : (∫ x, ((ρ x)⁻¹ * R x - ((ρ x)⁻¹ * fderiv ℝ ρ x v) * U x) * φ x ∂μ) =
      (∫ x, (ρ x)⁻¹ * R x * φ x ∂μ) - ∫ x, ((ρ x)⁻¹ * fderiv ℝ ρ x v) * U x * φ x ∂μ := by
    simp_rw [sub_mul]
    exact integral_sub hK hJ
  rw [hc]
  linarith

end DifferentialGeometry.Analysis.Sobolev
