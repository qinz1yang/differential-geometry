import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem setIntegral_mul_diffQuot_eq_neg_setIntegral_diffQuot_mul
    {Ω : Set E} {f g : E → ℝ} (k : Fin d) (h : ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hsupport : Function.support g ⊆ Ω)
    (htranslate : Function.support (translate k (-h) g) ⊆ Ω) :
    ∫ x in Ω, f x * diffQuot k (-h) g x =
      -∫ x in Ω, diffQuot k h f x * g x := by
  by_cases hh : h = 0
  · subst h
    simp
  have hg_zero (x : E) (hx : x ∉ Ω) : g x = 0 := by
    by_contra hne
    exact hx (hsupport hne)
  have hg_shift_zero (x : E) (hx : x ∉ Ω) :
      g (x + (-h) • EuclideanSpace.single k 1) = 0 := by
    by_contra hne
    exact hx (htranslate hne)
  have hleft (x : E) (hx : x ∉ Ω) : f x * diffQuot k (-h) g x = 0 := by
    rw [diffQuot_apply_of_ne k (neg_ne_zero.mpr hh), hg_shift_zero x hx, hg_zero x hx]
    ring
  have hright (x : E) (hx : x ∉ Ω) : diffQuot k h f x * g x = 0 := by
    rw [hg_zero x hx, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleft,
    setIntegral_eq_integral_of_forall_compl_eq_zero hright]
  have hibp := integral_diffQuot_mul_eq_neg_integral_mul_diffQuot k hh hf hg
  linarith

theorem setIntegral_mul_diffQuot_eq_neg_setIntegral_diffQuot_mul_of_cthickening_subset
    {Ω : Set E} {f g : E → ℝ} (k : Fin d) (h : ℝ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hroom : Metric.cthickening |h| (Function.support g) ⊆ Ω) :
    ∫ x in Ω, f x * diffQuot k (-h) g x =
      -∫ x in Ω, diffQuot k h f x * g x := by
  apply setIntegral_mul_diffQuot_eq_neg_setIntegral_diffQuot_mul k h hf hg
    ((Metric.self_subset_cthickening (Function.support g)).trans hroom)
  intro x hx
  apply hroom
  refine Metric.mem_cthickening_of_dist_le x
    (x + (-h) • EuclideanSpace.single k 1) |h| (Function.support g) hx ?_
  rw [dist_eq_norm, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg, norm_smul]
  simp

end DifferentialGeometry.Analysis.Sobolev
