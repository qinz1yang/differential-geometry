import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

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
