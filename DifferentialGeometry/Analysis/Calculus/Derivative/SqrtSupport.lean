import DifferentialGeometry.Analysis.Calculus.Derivative.Right
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

namespace DifferentialGeometry

open Set Filter
open scoped Topology

theorem sqrt_le_of_deriv_upper_support
    {f : ℝ → ℝ} {a b C : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hC : 0 ≤ C)
    (hsupport : ∀ t ∈ Ico a b, 0 < f t →
      ∃ phi : ℝ → ℝ, ∃ d : ℝ,
        phi t = f t ∧ f ≤ᶠ[𝓝[>] t] phi ∧
        HasDerivAt phi d t ∧ d ≤ 2 * C * Real.sqrt (f t)) :
    ∀ t ∈ Icc a b,
      Real.sqrt (f t) ≤ Real.sqrt (f a) + C * (t - a) := by
  intro t ht
  apply le_of_forall_pos_le_add
  intro delta hdelta
  let eps : ℝ := delta / (t - a + 1)
  have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
  have heps : 0 < eps := div_pos hdelta (by linarith)
  let g : ℝ → ℝ := fun r ↦ Real.sqrt (f r) - (C + eps) * (r - a)
  have hg : ContinuousOn g (Icc a b) :=
    hf.sqrt.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hga : g a ≤ Real.sqrt (f a) := by simp only [g, sub_self, mul_zero, sub_zero, le_refl]
  have hgt := le_of_upper_support hg hga (fun r hr hgr ↦ by
    have hfra : 0 < f r := by
      have hr0 : 0 ≤ r - a := sub_nonneg.mpr hr.1
      have hsqrt : 0 < Real.sqrt (f r) := by
        have hsub : 0 ≤ (C + eps) * (r - a) := mul_nonneg (by linarith) hr0
        have hs0 := Real.sqrt_nonneg (f a)
        dsimp only [g] at hgr
        linarith
      exact Real.sqrt_pos.mp hsqrt
    obtain ⟨phi, d, heq, hupper, hderiv, hd⟩ := hsupport r hr hfra
    have hphi : 0 < phi r := heq.symm ▸ hfra
    refine ⟨fun z ↦ Real.sqrt (phi z) - (C + eps) * (z - a),
      d / (2 * Real.sqrt (phi r)) - (C + eps), ?_, ?_, ?_, ?_⟩
    · simp only [heq, g]
    · filter_upwards [hupper] with z hz
      exact sub_le_sub_right (Real.sqrt_le_sqrt hz) _
    · convert (hderiv.sqrt hphi.ne').sub
        (((hasDerivAt_id r).sub_const a).const_mul (C + eps)) using 1 <;> first | rfl | simp only [mul_one]
    · have hroot : 0 < Real.sqrt (phi r) := Real.sqrt_pos.mpr hphi
      have hdiv : d / (2 * Real.sqrt (phi r)) ≤ C := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (phi r))).mpr
        rw [heq]
        nlinarith [hd]
      linarith) t ht
  have hsmall : eps * (t - a) ≤ delta := by
    dsimp only [eps]
    have hden : 0 < t - a + 1 := by linarith
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  dsimp only [g] at hgt
  nlinarith

end DifferentialGeometry
