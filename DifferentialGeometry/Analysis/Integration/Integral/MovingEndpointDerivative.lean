import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real


open Set Filter MeasureTheory
open scoped _root_.Topology Interval

namespace DifferentialGeometry.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem hasDerivAt_integral_from_base
    {F : ℝ → ℝ → E} {g : ℝ → ℝ} {x₀ g' : ℝ}
    (hF : ContinuousAt (fun p : ℝ × ℝ => F p.1 p.2) (x₀, g x₀))
    (hg : HasDerivAt g g' x₀)
    (hint : ∀ᶠ x in 𝓝 x₀, IntervalIntegrable (F x) volume (g x₀) (g x)) :
    HasDerivAt (fun x => ∫ t in g x₀..g x, F x t) (g' • F x₀ (g x₀)) x₀ := by
  have hrem : (fun x => ∫ t in g x₀..g x, F x t - F x₀ (g x₀))
      =o[𝓝 x₀] (fun x => g x - g x₀) := by
    refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hF ε hε
    filter_upwards [Metric.ball_mem_nhds x₀ hδ,
      hg.continuousAt.eventually (Metric.ball_mem_nhds (g x₀) hδ)] with x hx hgx
    have hnorm : ∀ t ∈ Ι (g x₀) (g x), ‖F x t - F x₀ (g x₀)‖ ≤ ε := by
      intro t ht
      have htclose : dist t (g x₀) < δ := by
        have hle : dist t (g x₀) ≤ dist (g x) (g x₀) := by
          simpa only [Real.dist_eq] using
            abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc ht)
        exact hle.trans_lt hgx
      have hpair : dist (x, t) (x₀, g x₀) < δ := by
        simpa only [Prod.dist_eq] using max_lt hx htclose
      simpa only [dist_eq_norm] using (hclose hpair).le
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_of_norm_le_const hnorm
  have hrem_deriv : HasDerivAt
      (fun x => ∫ t in g x₀..g x, F x t - F x₀ (g x₀)) 0 x₀ := by
    apply HasDerivAt.of_isLittleO
    simpa only [intervalIntegral.integral_same, sub_zero, smul_zero] using
      hrem.trans_isBigO hg.isBigO_sub
  have hlinear := (hg.sub_const (g x₀)).smul_const (F x₀ (g x₀))
  have hsum := hrem_deriv.add hlinear
  simp only [zero_add] at hsum
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hint] with x hx
  dsimp only [Pi.add_apply]
  rw [intervalIntegral.integral_sub hx intervalIntegrable_const,
    intervalIntegral.integral_const, sub_add_cancel]

theorem hasDerivAt_parametric_integral_right
    {F : ℝ → ℝ → E} {g : ℝ → ℝ} {a x₀ g' : ℝ} {d : E}
    (hF : ContinuousAt (fun p : ℝ × ℝ => F p.1 p.2) (x₀, g x₀))
    (hfixed : HasDerivAt (fun x => ∫ t in a..g x₀, F x t) d x₀)
    (hg : HasDerivAt g g' x₀)
    (hfixed_int : ∀ᶠ x in 𝓝 x₀, IntervalIntegrable (F x) volume a (g x₀))
    (hmoving_int : ∀ᶠ x in 𝓝 x₀, IntervalIntegrable (F x) volume (g x₀) (g x)) :
    HasDerivAt (fun x => ∫ t in a..g x, F x t) (d + g' • F x₀ (g x₀)) x₀ := by
  have hshort := hasDerivAt_integral_from_base hF hg hmoving_int
  apply (hfixed.add hshort).congr_of_eventuallyEq
  filter_upwards [hfixed_int, hmoving_int] with x hxi hxm
  exact (intervalIntegral.integral_add_adjacent_intervals hxi hxm).symm

theorem hasDerivAt_parametric_integral_add_right
    {F : ℝ → ℝ → E} {a b : ℝ} {d : E}
    (hF : ContinuousAt (fun p : ℝ × ℝ => F p.1 p.2) (0, b))
    (hfixed : HasDerivAt (fun x => ∫ t in a..b, F x t) d 0)
    (hfixed_int : ∀ᶠ x in 𝓝 0, IntervalIntegrable (F x) volume a b)
    (hmoving_int : ∀ᶠ x in 𝓝 0, IntervalIntegrable (F x) volume b (b + x)) :
    HasDerivAt (fun x => ∫ t in a..(b + x), F x t) (d + F 0 b) 0 := by
  simpa only [add_zero, one_smul] using
    hasDerivAt_parametric_integral_right (g := fun x : ℝ => b + x)
      (by simpa only [add_zero] using hF)
      (by simpa only [add_zero] using hfixed)
      ((hasDerivAt_id (0 : ℝ)).const_add b)
      (by simpa only [add_zero] using hfixed_int)
      (by simpa only [add_zero] using hmoving_int)

end DifferentialGeometry.Analysis.Calculus
