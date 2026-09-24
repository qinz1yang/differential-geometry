import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Filter MeasureTheory Set
open scoped Topology

theorem TendstoUniformlyOn.intervalIntegral
    {P E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter A} {J : Set P} {a b : ℝ}
    {f : A → ℝ × P → E} {g : ℝ × P → E}
    (hfg : TendstoUniformlyOn f g l (uIcc a b ×ˢ J))
    (hf : ∀ᶠ i in l, ∀ t ∈ J, IntervalIntegrable (fun x => f i (x, t)) volume a b)
    (hg : ∀ t ∈ J, IntervalIntegrable (fun x => g (x, t)) volume a b) :
    TendstoUniformlyOn (fun i t => ∫ x in a..b, f i (x, t))
      (fun t => ∫ x in a..b, g (x, t)) l J := by
  rw [Metric.tendstoUniformlyOn_iff] at hfg ⊢
  intro ε hε
  have hden : 0 < 2 * (|b - a| + 1) := by positivity
  have hδ : 0 < ε / (2 * (|b - a| + 1)) := div_pos hε hden
  filter_upwards [hf, hfg (ε / (2 * (|b - a| + 1))) hδ] with i hi hclose t ht
  rw [dist_eq_norm, norm_sub_rev, ← intervalIntegral.integral_sub (hi t ht) (hg t ht)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := ε / (2 * (|b - a| + 1))) (fun x hx => ?_)).trans_lt ?_
  · exact (by simpa only [dist_eq_norm, norm_sub_rev] using
      (hclose (x, t) ⟨uIoc_subset_uIcc hx, ht⟩).le)
  · have hmul : ε / (2 * (|b - a| + 1)) * (2 * (|b - a| + 1)) = ε :=
      div_mul_cancel₀ ε hden.ne'
    nlinarith [abs_nonneg (b - a)]

end

section

open MeasureTheory Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem tendsto_integral_mul_of_tendstoUniformlyOn_Icc
    {f : ℕ → ℝ → ℝ} {v g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ n, ContinuousOn (f n) (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hlim : TendstoUniformlyOn f v atTop (Icc a b)) :
    Tendsto (fun n => ∫ x in Ioo a b, f n x * g x) atTop
      (𝓝 (∫ x in Ioo a b, v x * g x)) := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  let C := max D 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hprod : TendstoUniformlyOn (fun n x => f n x * g x) (fun x => v x * g x)
      atTop (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim (ε / C) (div_pos hε hC)] with n hn
    intro x hx
    rw [Real.dist_eq, ← sub_mul, abs_mul]
    have hfg : |v x - f n x| < ε / C := by simpa only [Real.dist_eq] using hn x hx
    have hgc : |g x| ≤ C := by
      have h := hD x hx
      rw [Real.norm_eq_abs] at h
      exact h.trans (by dsimp [C]; linarith [le_max_left D 0])
    calc
      |v x - f n x| * |g x| ≤ |v x - f n x| * C :=
        mul_le_mul_of_nonneg_left hgc (abs_nonneg _)
      _ < ε := (lt_div_iff₀ hC).mp hfg
  have hprod' : TendstoUniformlyOn (fun n x => f n x * g x) (fun x => v x * g x)
      atTop (uIcc a b) := by simpa only [uIcc_of_le hab] using hprod
  have hFG : ∀ n, ContinuousOn (fun x => f n x * g x) (uIcc a b) := by
    intro n x hx
    rw [uIcc_of_le hab] at hx ⊢
    exact (hf n x hx).mul (hg x hx)
  have hh := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) (a := a) (b := b)
    (Eventually.of_forall hFG) hprod'
  simpa only [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] using hh

end DifferentialGeometry.Analysis

end
