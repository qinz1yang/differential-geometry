import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeWeakDerivativeProduct
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Regularity.C1Representative

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ν : Measure E} [IsLocallyFiniteMeasure ν] {Ω : Set E} {a b : ℝ}

theorem exists_contDiffOn_timeH1_of_second_spacetime_weak_deriv
    (hab : a < b) (hΩ : IsOpen Ω)
    (U R S : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (ν.restrict Ω)))
    (hU : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, U p * fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (ν.restrict Ω)) =
        -∫ p, R p * φ p ∂(volume.restrict (Icc a b)).prod (ν.restrict Ω))
    (hR : ∀ φ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ω →
      (∫ p, R p * fderiv ℝ φ p (1, 0) ∂(volume.restrict (Icc a b)).prod (ν.restrict Ω)) =
        -∫ p, S p * φ p ∂(volume.restrict (Icc a b)).prod (ν.restrict Ω)) :
    ∃ u v : timeH1 (Lp ℝ 2 (ν.restrict Ω)) (b - a),
      (∀ᵐ t ∂timeMeasure (b - a),
        ((u.toFun t : E → ℝ) =ᵐ[ν.restrict Ω] fun x => U (a + t, x)) ∧
        ((v.toFun t : E → ℝ) =ᵐ[ν.restrict Ω] fun x => R (a + t, x)) ∧
        ((v.deriv t : E → ℝ) =ᵐ[ν.restrict Ω] fun x => S (a + t, x))) ∧
      u.deriv = v.toFunL2 ∧
      ContDiffOn ℝ 1 u.toFun (Icc (0 : ℝ) (b - a)) ∧
      EqOn (derivWithin u.toFun (Icc (0 : ℝ) (b - a))) v.toFun (Icc (0 : ℝ) (b - a)) := by
  obtain ⟨u, hu⟩ := exists_timeH1_of_spacetime_weak_deriv hab hΩ U R hU
  obtain ⟨v, hv⟩ := exists_timeH1_of_spacetime_weak_deriv hab hΩ R S hR
  have hrep : u.deriv =ᵐ[timeMeasure (b - a)] v.toFun := by
    filter_upwards [hu, hv] with t ht hs
    apply Lp.ext
    exact Filter.EventuallyEq.trans ht.2 (Filter.EventuallyEq.symm hs.1)
  have heq : u.deriv = v.toFunL2 := by
    apply Lp.ext
    exact Filter.EventuallyEq.trans hrep
      (Filter.EventuallyEq.symm (coeFn_ofContinuousOn v.continuousOn_toFun))
  refine ⟨u, v, ?_, heq, toFun_c1_of_rep (sub_pos.mpr hab) u v.toFun v.continuousOn_toFun hrep⟩
  filter_upwards [hu, hv] with t ht hs
  exact ⟨ht.1, hs⟩

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
