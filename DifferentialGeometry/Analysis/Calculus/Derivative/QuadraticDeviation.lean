import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations


noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_sub_le_mul_sq_of_second_deriv_sub_le
    {f g : ℝ → E} {r K : ℝ}
    (hf : ∀ t ∈ uIcc 0 r, DifferentiableAt ℝ f t)
    (hg : ∀ t ∈ uIcc 0 r, DifferentiableAt ℝ g t)
    (hf' : ∀ t ∈ uIcc 0 r, DifferentiableAt ℝ (deriv f) t)
    (hg' : ∀ t ∈ uIcc 0 r, DifferentiableAt ℝ (deriv g) t)
    (hvalue : f 0 = g 0) (hvelocity : deriv f 0 = deriv g 0)
    (hsecond : ∀ t ∈ uIcc 0 r, ‖deriv (deriv f) t - deriv (deriv g) t‖ ≤ K) :
    ‖f r - g r‖ ≤ K * r ^ 2 := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hsecond 0 left_mem_uIcc)
  have hfirst : ∀ t ∈ uIcc 0 r, ‖deriv f t - deriv g t‖ ≤ K * ‖r‖ := by
    intro t ht
    have h := (convex_uIcc (0 : ℝ) r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => ((hf' s hs).hasDerivAt.sub (hg' s hs).hasDerivAt).hasDerivWithinAt)
      hsecond left_mem_uIcc ht
    have htNorm : ‖t‖ ≤ ‖r‖ := by
      simp only [Real.norm_eq_abs]
      exact abs_le.mpr
        ⟨(le_min (neg_nonpos.mpr (abs_nonneg r)) (neg_abs_le r)).trans ht.1,
          ht.2.trans (max_le (abs_nonneg r) (le_abs_self r))⟩
    have h' : ‖deriv f t - deriv g t‖ ≤ K * ‖t‖ := by
      simpa only [Pi.sub_apply, hvelocity, sub_self, sub_zero] using h
    exact h'.trans (mul_le_mul_of_nonneg_left htNorm hK)
  have h := (convex_uIcc (0 : ℝ) r).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => ((hf t ht).hasDerivAt.sub (hg t ht).hasDerivAt).hasDerivWithinAt)
    hfirst left_mem_uIcc right_mem_uIcc
  simpa only [Pi.sub_apply, hvalue, sub_self, sub_zero, Real.norm_eq_abs, mul_assoc,
    ← pow_two, sq_abs] using h

theorem norm_sub_le_mul_sq_of_contDiffAt
    {f g : ℝ → E} {r K : ℝ}
    (hf : ∀ t ∈ uIcc 0 r, ContDiffAt ℝ 2 f t)
    (hg : ∀ t ∈ uIcc 0 r, ContDiffAt ℝ 2 g t)
    (hvalue : f 0 = g 0) (hvelocity : deriv f 0 = deriv g 0)
    (hsecond : ∀ t ∈ uIcc 0 r, ‖deriv (deriv f) t - deriv (deriv g) t‖ ≤ K) :
    ‖f r - g r‖ ≤ K * r ^ 2 :=
  norm_sub_le_mul_sq_of_second_deriv_sub_le
    (fun t ht => (hf t ht).differentiableAt (by norm_num))
    (fun t ht => (hg t ht).differentiableAt (by norm_num))
    (fun t ht => ((hf t ht).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num))
    (fun t ht => ((hg t ht).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num))
    hvalue hvelocity hsecond

theorem eventually_norm_sub_le_mul_sq_of_second_deriv_sub_le
    {f g : ℝ → E} {K : ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0)
    (hvalue : f 0 = g 0) (hvelocity : deriv f 0 = deriv g 0)
    (hsecond : ∀ᶠ t in 𝓝 (0 : ℝ),
      ‖deriv (deriv f) t - deriv (deriv g) t‖ ≤ K) :
    ∀ᶠ r in 𝓝 (0 : ℝ), ‖f r - g r‖ ≤ K * r ^ 2 := by
  have hall := (hf.eventually (by norm_num)).and
    ((hg.eventually (by norm_num)).and hsecond)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hall
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with r hr
  have hseg : uIcc 0 r ⊆ Metric.ball (0 : ℝ) ε := by
    simpa only [segment_eq_uIcc] using
      (convex_ball (0 : ℝ) ε).segment_subset (Metric.mem_ball_self hε) hr
  exact norm_sub_le_mul_sq_of_contDiffAt
    (fun t ht => (hball (hseg ht)).1)
    (fun t ht => (hball (hseg ht)).2.1) hvalue hvelocity
    (fun t ht => (hball (hseg ht)).2.2)


theorem norm_sub_affine_le_mul_sq_of_second_deriv_le
    {γ : ℝ → E} {v w : E} {r K : ℝ}
    (hγ : ∀ t ∈ uIcc 0 r, ContDiffAt ℝ 2 γ t)
    (hvalue : γ 0 = v) (hvelocity : deriv γ 0 = w)
    (hsecond : ∀ t ∈ uIcc 0 r, ‖deriv (deriv γ) t‖ ≤ K) :
    ‖γ r - (v + r • w)‖ ≤ K * r ^ 2 := by
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => v + s • w) w t := by
    simpa only [id_eq, one_smul, zero_add] using
      ((hasDerivAt_id t).smul_const w).const_add v
  have hlineDeriv : deriv (fun s : ℝ => v + s • w) = fun _ => w :=
    funext fun t => (hline t).deriv
  apply norm_sub_le_mul_sq_of_contDiffAt (g := fun r : ℝ => v + r • w) hγ
    (fun _ _ => by simpa only [id_eq] using
      contDiffAt_const.add (contDiffAt_id.smul_const w))
  · simpa only [zero_smul, add_zero] using hvalue
  · simpa only [hlineDeriv] using hvelocity
  · intro t ht
    simpa only [hlineDeriv, deriv_const, sub_zero] using hsecond t ht


theorem eventually_norm_sub_affine_le_of_second_deriv_bound_at_zero
    {γ : ℝ → E} {v w : E} {C : ℝ}
    (hγ : ContDiffAt ℝ 2 γ 0) (hw : w ≠ 0)
    (hvalue : γ 0 = v) (hvelocity : deriv γ 0 = w)
    (hsecond : ‖deriv (deriv γ) 0‖ ≤ C * ‖w‖ ^ 2) :
    ∀ᶠ r in 𝓝 (0 : ℝ),
      ‖γ r - (v + r • w)‖ ≤ (C + 1) * ‖w‖ ^ 2 * r ^ 2 := by
  have hwpos : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have hγ' : ContDiffAt ℝ 1 (deriv γ) 0 := hγ.derivWithin (by norm_num)
  have hγ'' : ContinuousAt (deriv (deriv γ)) 0 :=
    (hγ'.derivWithin (m := 0) (by norm_num)).continuousAt
  have hstrict : ‖deriv (deriv γ) 0‖ < (C + 1) * ‖w‖ ^ 2 := by
    nlinarith only [hsecond, hwpos]
  have hbound : ∀ᶠ t in 𝓝 (0 : ℝ),
      ‖deriv (deriv γ) t‖ ≤ (C + 1) * ‖w‖ ^ 2 :=
    (hγ''.norm.eventually_lt_const hstrict).mono fun _ h => h.le
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => v + s • w) w t := by
    simpa only [id_eq, one_smul, zero_add] using
      ((hasDerivAt_id t).smul_const w).const_add v
  have hlineDeriv : deriv (fun s : ℝ => v + s • w) = fun _ => w :=
    funext fun t => (hline t).deriv
  apply eventually_norm_sub_le_mul_sq_of_second_deriv_sub_le
    (g := fun r : ℝ => v + r • w) hγ
    (by simpa only [id_eq] using contDiffAt_const.add (contDiffAt_id.smul_const w))
  · simpa only [zero_smul, add_zero] using hvalue
  · simpa only [hlineDeriv] using hvelocity
  · simpa only [hlineDeriv, deriv_const, sub_zero] using hbound

end DifferentialGeometry.Analysis
