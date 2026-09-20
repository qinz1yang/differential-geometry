import DifferentialGeometry.Analysis.Sobolev.WeakDerivativeCommutation
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
variable {μ : Measure E} [IsLocallyFiniteMeasure μ]

theorem exists_lp_weak_deriv_of_ae_eq_finite_sum
    {ι : Type*} [Fintype ι] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω) (v : E)
    (f : Lp ℝ p μ) (Y Z : ι → Lp ℝ p μ) (A : ι → E → ℝ)
    (hA : ∀ i, MemLp (A i) ∞ μ)
    (hDA : ∀ i, MemLp (fun x => fderiv ℝ (A i) x v) ∞ μ)
    (hAsmooth : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (A i) Ω)
    (hYweak : ∀ i, ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, Y i x * fderiv ℝ φ x v ∂μ) = -∫ x, Z i x * φ x ∂μ)
    (hf : f =ᵐ[μ] fun x => ∑ i, A i x * Y i x) :
    ∃ R : Lp ℝ p μ,
      (R =ᵐ[μ] fun x => ∑ i,
        (A i x * Z i x + fderiv ℝ (A i) x v * Y i x)) ∧
      ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ω →
        (∫ x, f x * fderiv ℝ φ x v ∂μ) = -∫ x, R x * φ x ∂μ := by
  let S : ι → E → ℝ := fun i x =>
    A i x * Z i x + fderiv ℝ (A i) x v * Y i x
  have hS (i) : MemLp (S i) p μ :=
    ((Lp.memLp (Z i)).mul (hA i)).add ((Lp.memLp (Y i)).mul (hDA i))
  have hsum : MemLp (fun x => ∑ i, S i x) p μ :=
    memLp_finsetSum Finset.univ fun i _ => hS i
  let R := hsum.toLp (fun x => ∑ i, S i x)
  have hR : R =ᵐ[μ] fun x => ∑ i, S i x := hsum.coeFn_toLp
  refine ⟨R, hR, ?_⟩
  intro φ hφ hφc hφs
  have hI (i) : Integrable (fun x => A i x * Y i x * fderiv ℝ φ x v) μ :=
    (((Lp.memLp (Y i)).mul (r := p) (hA i)).locallyIntegrable hp)
      |>.integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hφc.fderiv_apply ℝ v)
  have hJ (i) : Integrable (fun x => S i x * φ x) μ :=
    (hS i).locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc
  calc
    (∫ x, f x * fderiv ℝ φ x v ∂μ) =
        ∫ x, (∑ i, A i x * Y i x) * fderiv ℝ φ x v ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
    _ = ∑ i, ∫ x, A i x * Y i x * fderiv ℝ φ x v ∂μ := by
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ fun i _ => hI i
    _ = -∑ i, ∫ x, S i x * φ x ∂μ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_weak_product_deriv hΩ v
        ((Lp.memLp (Y i)).locallyIntegrable hp)
        ((Lp.memLp (Z i)).locallyIntegrable hp)
        (hAsmooth i) (hYweak i) hφ hφc hφs
    _ = -(∫ x, (∑ i, S i x) * φ x ∂μ) := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ fun i _ => hJ i]
    _ = -∫ x, R x * φ x ∂μ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hR] with x hx
      rw [hx]

end DifferentialGeometry.Analysis.Sobolev
