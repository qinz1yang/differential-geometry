import DifferentialGeometry.Geometry.Operator.Family.Gram.Curve
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.H1
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open Filter Function MeasureTheory Set
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {D : RealTimeInterval}

theorem chartGramOp_inner_deriv_ae_of_timeH1
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (τ : ℝ → ℝ) (γ : ℝ → M) (p : M) (a b : ℝ)
    (u : timeH1 E (b - a))
    (hsrc : MapsTo γ (Icc a b) (chartAt H p).source)
    (hrep : EqOn u.toFun (fun r => extChartAt I p (γ (a + r))) (Icc 0 (b - a))) :
    (fun r => inner ℝ (chartGramOp G p (τ (a + r), u.toFun r) (u.deriv r))
      (u.deriv r)) =ᵐ[timeMeasure (b - a)]
    fun r => (G.metric (τ (a + r))).inner (γ (a + r))
      ((mfderiv 𝓘(ℝ, ℝ) I γ (a + r)) (1 : ℝ))
      ((mfderiv 𝓘(ℝ, ℝ) I γ (a + r)) (1 : ℝ)) := by
  by_cases hab : a ≤ b
  · have hdiff := curve_mdiff_local I p γ u hab hsrc hrep
    have hmem : ∀ᵐ r ∂timeMeasure (b - a), r ∈ Ioo 0 (b - a) := by
      unfold timeMeasure
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [u.ae_hasDerivWithinAt_toFun, hdiff, hmem] with r hu hγ hr
    have hrcc : r ∈ Icc 0 (b - a) := ⟨hr.1.le, hr.2.le⟩
    have hnhds : Icc 0 (b - a) ∈ 𝓝 r := Icc_mem_nhds hr.1 hr.2
    have hcoord : HasDerivAt (fun s => extChartAt I p (γ (a + s))) (u.deriv r) r := by
      apply hu.hasDerivAt hnhds |>.congr_of_eventuallyEq
      filter_upwards [hnhds] with s hs
      exact (hrep hs).symm
    have hderiv : deriv ((extChartAt I p) ∘ γ) (a + r) = u.deriv r := by
      rw [← deriv_comp_const_add]
      exact hcoord.deriv
    have hpoint := chartGramOp_inner_deriv G p (τ (a + r)) hγ
      (hsrc ⟨le_add_of_nonneg_right hrcc.1, by linarith [hrcc.2]⟩)
    simpa only [hderiv, hrep hrcc] using hpoint
  · have hneg : b - a < 0 := sub_neg.mpr (lt_of_not_ge hab)
    simp only [timeMeasure, Icc_eq_empty_of_lt hneg, Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot

theorem integral_mul_inner_mfderiv_eq_integral_chartGramOp_of_timeH1
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (τ w : ℝ → ℝ) (γ : ℝ → M) (p : M) (a b : ℝ) (hab : a ≤ b)
    (u : timeH1 E (b - a))
    (hsrc : MapsTo γ (Icc a b) (chartAt H p).source)
    (hrep : EqOn u.toFun (fun r => extChartAt I p (γ (a + r))) (Icc 0 (b - a))) :
    (∫ s in a..b, w s * (G.metric (τ s)).inner (γ s)
      ((mfderiv 𝓘(ℝ, ℝ) I γ s) (1 : ℝ))
      ((mfderiv 𝓘(ℝ, ℝ) I γ s) (1 : ℝ))) =
    ∫ r in (0 : ℝ)..b - a, w (a + r) *
      inner ℝ (chartGramOp G p (τ (a + r), u.toFun r) (u.deriv r)) (u.deriv r) := by
  let F : ℝ → ℝ := fun s => w s * (G.metric (τ s)).inner (γ s)
    ((mfderiv 𝓘(ℝ, ℝ) I γ s) (1 : ℝ))
    ((mfderiv 𝓘(ℝ, ℝ) I γ s) (1 : ℝ))
  have hshift : (∫ r in (0 : ℝ)..b - a, F (a + r)) = ∫ s in a..b, F s := by
    simpa only [add_comm a, zero_add, sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right F (a := 0) (b := b - a) a)
  change (∫ s in a..b, F s) = _
  rw [← hshift]
  apply intervalIntegral.integral_congr_ae_restrict
  have heq := chartGramOp_inner_deriv_ae_of_timeH1 G τ γ p a b u hsrc hrep
  have hweighted : (fun r => F (a + r)) =ᵐ[timeMeasure (b - a)]
      fun r => w (a + r) *
        inner ℝ (chartGramOp G p (τ (a + r), u.toFun r) (u.deriv r)) (u.deriv r) :=
    heq.mono fun r hr => congrArg (w (a + r) * ·) hr.symm
  simpa only [timeMeasure, uIoc_of_le (sub_nonneg.mpr hab),
    restrict_Ioc_eq_restrict_Icc] using hweighted

end DifferentialGeometry.Geometry.Curvature
