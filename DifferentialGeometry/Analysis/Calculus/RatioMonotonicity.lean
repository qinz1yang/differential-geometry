import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Monotonicity of a quotient from a cross-derivative inequality

This file records the scalar calculus step used by relative comparison
arguments.  Geometric applications prove the cross-multiplied logarithmic
derivative inequality and use this result without introducing logarithms.
-/

open MeasureTheory Set

/-- If `f' * g <= f * g'` and `g` is positive on an open interval, then
`f / g` is antitone there. -/
theorem ratio_anti_of_cross
    {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hgpos : ∀ x ∈ Ioo a b, 0 < g x)
    (hcross : ∀ x ∈ Ioo a b, f' x * g x ≤ f x * g' x) :
    AntitoneOn (fun x => f x / g x) (Ioo a b) := by
  have hdiff : DifferentiableOn ℝ (fun x => f x / g x) (Ioo a b) := by
    intro x hx
    exact DifferentiableAt.differentiableWithinAt
      ((hf x hx).fun_div (hg x hx) (ne_of_gt (hgpos x hx))).differentiableAt
  refine antitoneOn_of_deriv_nonpos (convex_Ioo a b) hdiff.continuousOn ?_ ?_
  · simpa using hdiff
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa using hx
    rw [((hf x hx').fun_div (hg x hx') (ne_of_gt (hgpos x hx'))).deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hcross x hx')) (sq_nonneg (g x))

/-- If the pointwise ratio `f / g` is antitone and `g` is positive, then the
ratio of the integrals from zero is antitone as well. -/
theorem integralRatio_anti
    {f g : ℝ → ℝ} {b : ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hgpos : ∀ x ∈ Ioo (0 : ℝ) b, 0 < g x)
    (hratio : AntitoneOn (fun x => f x / g x) (Ioo (0 : ℝ) b)) :
    AntitoneOn
      (fun r => (∫ x in 0..r, f x) / ∫ x in 0..r, g x)
      (Ioo (0 : ℝ) b) := by
  refine ratio_anti_of_cross (f' := f) (g' := g) ?_ ?_ ?_ ?_
  · intro r _hr
    exact intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable 0 r)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  · intro r _hr
    exact intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 r)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  · intro r hr
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hg.intervalIntegrable 0 r)
      (fun x hx => hgpos x ⟨hx.1, hx.2.trans hr.2⟩) hr.1
  · intro r hr
    have hpoint : ∀ x ∈ Ioo (0 : ℝ) r,
        f r * g x ≤ g r * f x := by
      intro x hx
      have hxb : x ∈ Ioo (0 : ℝ) b := ⟨hx.1, hx.2.trans hr.2⟩
      have hdiv := hratio hxb hr hx.2.le
      have hmul := (div_le_div_iff₀ (hgpos r hr) (hgpos x hxb)).mp hdiv
      simpa only [mul_comm] using hmul
    have hleft : Continuous (fun x : ℝ => f r * g x) := continuous_const.mul hg
    have hright : Continuous (fun x : ℝ => g r * f x) := continuous_const.mul hf
    have hint := intervalIntegral.integral_mono_on_of_le_Ioo
      (μ := volume) hr.1.le
      (hleft.intervalIntegrable (μ := volume) 0 r)
      (hright.intervalIntegrable (μ := volume) 0 r) hpoint
    simpa only [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, mul_comm] using hint
