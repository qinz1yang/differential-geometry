import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped BigOperators

namespace DifferentialGeometry.Analysis.Parabolic

theorem integral_weighted_flux_eq_of_residual_eq_zero
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {u w timeDerivative : α → ℝ} {A : α → ι → ι → ℝ}
    {du df testGradient : ι → α → ℝ}
    (hgradient : ∀ᵐ p ∂μ, ∀ i, du i p = -u p * df i p)
    (htime : Integrable (fun p => w p * u p * timeDerivative p) μ)
    (hflux : ∀ j, Integrable
      (fun p => (∑ i, w p * A p i j * du i p) * testGradient j p) μ)
    (hresidual : (∫ p, w p * u p *
      (timeDerivative p + ∑ j, ∑ i, A p i j * df i p * testGradient j p) ∂μ) = 0) :
    (∫ p, w p * u p * timeDerivative p ∂μ) =
      ∑ j, ∫ p, (∑ i, w p * A p i j * du i p) * testGradient j p ∂μ := by
  have hsum : Integrable
      (fun p => ∑ j, (∑ i, w p * A p i j * du i p) * testGradient j p) μ :=
    integrable_finsetSum Finset.univ fun j _ => hflux j
  have hconvert :
      (fun p => w p * u p *
        (timeDerivative p + ∑ j, ∑ i, A p i j * df i p * testGradient j p)) =ᵐ[μ]
      fun p => w p * u p * timeDerivative p -
        ∑ j, (∑ i, w p * A p i j * du i p) * testGradient j p := by
    filter_upwards [hgradient] with p hp
    have hsum_eq :
        (∑ j, (∑ i, w p * A p i j * du i p) * testGradient j p) =
          -(w p * u p * (∑ j, ∑ i, A p i j * df i p * testGradient j p)) := by
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hp i]
      ring
    rw [hsum_eq]
    ring
  have hzero :
      (∫ p, w p * u p * timeDerivative p -
        ∑ j, (∑ i, w p * A p i j * du i p) * testGradient j p ∂μ) = 0 :=
    (integral_congr_ae hconvert).symm.trans hresidual
  rw [integral_sub htime hsum,
    integral_finsetSum Finset.univ (fun j _ => hflux j)] at hzero
  exact sub_eq_zero.mp hzero

end DifferentialGeometry.Analysis.Parabolic
