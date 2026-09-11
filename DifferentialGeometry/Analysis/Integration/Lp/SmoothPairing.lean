import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

theorem Lp.eq_of_integral_contDiff_mul_dual_eq_on_denseRange
    {A X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ι : A → X) (hι : DenseRange ι)
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (L₁ L₂ : Lp (X →L[ℝ] ℝ) p μ)
    (h : ∀ (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ x : A, (∫ t, φ t * L₁ t (ι x) ∂μ) = ∫ t, φ t * L₂ t (ι x) ∂μ) :
    L₁ = L₂ := by
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp L₁).locallyIntegrable hp)
    ((Lp.memLp L₂).locallyIntegrable hp)
  intro φ hφ hφc
  have hint (L : Lp (X →L[ℝ] ℝ) p μ) : Integrable (fun t => φ t • L t) μ :=
    ((Lp.memLp L).locallyIntegrable hp).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hφc
  apply DFunLike.coe_injective
  apply hι.equalizer (∫ t, φ t • L₁ t ∂μ).continuous (∫ t, φ t • L₂ t ∂μ).continuous
  funext x
  simp only [Function.comp_apply]
  rw [ContinuousLinearMap.integral_apply (hint L₁),
    ContinuousLinearMap.integral_apply (hint L₂)]
  exact h φ hφ hφc x

end MeasureTheory
