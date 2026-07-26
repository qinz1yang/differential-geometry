import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.GroupWithZero.Indicator

/-!
# Weighted non-injective area inequality

This file records the weighted, non-injective change-of-variables *inequality* for a
map `f : E → E` differentiable on a measurable set `s` of a finite-dimensional real
normed space carrying an additive Haar measure.

Mathlib provides the unweighted, injectivity-free bound
`MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv` and the weighted change of
variables *equality* only under injectivity
(`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`). The weighted
non-injective inequality below is not otherwise available.

## Main result

* `MeasureTheory.image_lintegral_le`: for a measurable weight `w : E → ℝ≥0∞`,
  `∫⁻ y in f '' s, w y ∂μ ≤ ∫⁻ x in s, w (f x) * ENNReal.ofReal |(f' x).det| ∂μ`.

The Jacobian weight `x ↦ |(f' x).det|` is **not** assumed measurable: the proof lifts
the per-set Mathlib bound to simple functions using the unconditional superadditivity
`MeasureTheory.le_lintegral_add`, then to a general `w` by monotone convergence on the
image side only, so the weight is never moved across a limit.
-/

open MeasureTheory MeasureTheory.Measure Set Module
open scoped ENNReal NNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
  {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [IsAddHaarMeasure μ] in
/-- Simple-function stage of `image_lintegral_le`: given the per-set image bound `hkey`
(the injectivity-free Mathlib inequality with weight `d`), the area inequality holds for
every simple function `φ` in place of the weight. The weight `d` is arbitrary — in
particular not assumed measurable — which is why the additive step is discharged with the
unconditional `le_lintegral_add` rather than `lintegral_add_left`. -/
private lemma image_simpleFunc_le (hf : Measurable f) {d : E → ℝ≥0∞}
    (hkey : ∀ ⦃T : Set E⦄, MeasurableSet T →
      μ (f '' s ∩ T) ≤ ∫⁻ x in s ∩ f ⁻¹' T, d x ∂μ)
    (φ : SimpleFunc E ℝ≥0∞) :
    ∫⁻ y in f '' s, φ y ∂μ ≤ ∫⁻ x in s, φ (f x) * d x ∂μ := by
  induction φ using SimpleFunc.induction with
  | @const c T hT =>
    have hcoe : ⇑(SimpleFunc.piecewise T hT (SimpleFunc.const E c) (SimpleFunc.const E 0))
        = T.indicator (fun _ => c) := by
      funext z
      by_cases hz : z ∈ T <;>
        simp [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, Set.piecewise, Set.indicator,
          Function.const, hz]
    simp only [hcoe]
    have hRHS : ∫⁻ x in s, T.indicator (fun _ => c) (f x) * d x ∂μ
        = ∫⁻ x in s ∩ f ⁻¹' T, c * d x ∂μ := by
      have h1 : ∀ x, T.indicator (fun _ => c) (f x) * d x
          = (f ⁻¹' T).indicator (fun z => c * d z) x := by
        intro x
        have hA : T.indicator (fun _ => c) (f x) = (f ⁻¹' T).indicator (fun _ => c) x := rfl
        rw [hA]
        exact (Set.indicator_mul_left (f ⁻¹' T) (fun _ => c) d).symm
      simp only [h1]
      rw [lintegral_indicator (hf hT), Measure.restrict_restrict (hf hT),
        Set.inter_comm (f ⁻¹' T) s]
    rw [lintegral_indicator hT, setLIntegral_const, Measure.restrict_apply hT, hRHS]
    calc c * μ (T ∩ f '' s)
        = c * μ (f '' s ∩ T) := by rw [Set.inter_comm]
      _ ≤ c * ∫⁻ x in s ∩ f ⁻¹' T, d x ∂μ := by gcongr; exact hkey hT
      _ ≤ ∫⁻ x in s ∩ f ⁻¹' T, c * d x ∂μ := lintegral_const_mul_le c _
  | @add φ₁ φ₂ _ h₁ h₂ =>
    have hL : ∫⁻ y in f '' s, (φ₁ + φ₂) y ∂μ
        = (∫⁻ y in f '' s, φ₁ y ∂μ) + ∫⁻ y in f '' s, φ₂ y ∂μ := by
      simp only [SimpleFunc.coe_add, Pi.add_apply]
      exact lintegral_add_left φ₁.measurable _
    have hR : (∫⁻ x in s, φ₁ (f x) * d x ∂μ) + ∫⁻ x in s, φ₂ (f x) * d x ∂μ
        ≤ ∫⁻ x in s, (φ₁ + φ₂) (f x) * d x ∂μ := by
      simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
      exact le_lintegral_add _ _
    calc ∫⁻ y in f '' s, (φ₁ + φ₂) y ∂μ
        = _ := hL
      _ ≤ _ := add_le_add h₁ h₂
      _ ≤ _ := hR

/-- **Weighted non-injective area inequality.** For an additive Haar measure `μ` on a
finite-dimensional real normed space `E`, a measurable set `s`, a measurable map
`f : E → E` differentiable within `s` with derivative `f'`, and a measurable weight
`w : E → ℝ≥0∞`, the `w`-weighted measure of the image `f '' s` is at most the integral
over `s` of `w ∘ f` weighted by the Jacobian `|det f'|`. No injectivity is assumed. -/
theorem image_lintegral_le
    (hs : MeasurableSet s) (hf : Measurable f)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    {w : E → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ y in f '' s, w y ∂μ ≤
      ∫⁻ x in s, w (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by
  have hkey : ∀ ⦃T : Set E⦄, MeasurableSet T →
      μ (f '' s ∩ T) ≤ ∫⁻ x in s ∩ f ⁻¹' T, ENNReal.ofReal |(f' x).det| ∂μ := by
    intro T hT
    rw [← Set.image_inter_preimage]
    exact addHaar_image_le_lintegral_abs_det_fderiv μ (hs.inter (hf hT))
      (fun x hx => (hf' x hx.1).mono Set.inter_subset_left)
  have key := image_simpleFunc_le μ hf hkey
  calc ∫⁻ y in f '' s, w y ∂μ
      = ∫⁻ y in f '' s, ⨆ n, (SimpleFunc.eapprox w n : E → ℝ≥0∞) y ∂μ :=
        lintegral_congr (fun y => (SimpleFunc.iSup_eapprox_apply hw y).symm)
    _ = ⨆ n, ∫⁻ y in f '' s, (SimpleFunc.eapprox w n : E → ℝ≥0∞) y ∂μ :=
        lintegral_iSup (fun n => (SimpleFunc.eapprox w n).measurable)
          (fun i j h a => SimpleFunc.monotone_eapprox w h a)
    _ ≤ ∫⁻ x in s, w (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by
        refine iSup_le (fun n => (key (SimpleFunc.eapprox w n)).trans ?_)
        refine lintegral_mono (fun x => ?_)
        have hle : (SimpleFunc.eapprox w n : E → ℝ≥0∞) (f x) ≤ w (f x) :=
          calc (SimpleFunc.eapprox w n : E → ℝ≥0∞) (f x)
              ≤ ⨆ m, (SimpleFunc.eapprox w m : E → ℝ≥0∞) (f x) :=
                le_iSup (fun m => (SimpleFunc.eapprox w m : E → ℝ≥0∞) (f x)) n
            _ = w (f x) := SimpleFunc.iSup_eapprox_apply hw (f x)
        gcongr

end MeasureTheory
