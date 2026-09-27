import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring

open Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.Calculus

theorem exists_upper_support_of_exp_reparametrization
    {C φ : ℝ → ℝ} {c b d : ℝ} (hcb : c < b)
    (hφ : φ 0 = C b)
    (hupper : ∀ᶠ u in 𝓝 (0 : ℝ), C (c + Real.exp u * (b - c)) ≤ φ u)
    (hφderiv : HasDerivAt φ ((b - c) * d) 0) :
    ∃ ψ : ℝ → ℝ, ψ b = C b ∧ C ≤ᶠ[𝓝 b] ψ ∧ HasDerivAt ψ d b := by
  have hbc : 0 < b - c := sub_pos.mpr hcb
  have hbc0 : b - c ≠ 0 := hbc.ne'
  let χ : ℝ → ℝ := fun r => Real.log ((r - c) / (b - c))
  have hχb : χ b = 0 := by
    simp only [χ, div_self hbc0, Real.log_one]
  have hquot : HasDerivAt (fun r : ℝ => (r - c) / (b - c))
      (1 / (b - c)) b :=
    ((hasDerivAt_id b).sub_const c).div_const (b - c)
  have hχderiv : HasDerivAt χ (b - c)⁻¹ b := by
    have hnonzero : (b - c) / (b - c) ≠ 0 := by
      rw [div_self hbc0]
      exact one_ne_zero
    simpa only [χ, div_self hbc0, div_one, one_div] using hquot.log hnonzero
  have hχtendsto : Tendsto χ (𝓝 b) (𝓝 (0 : ℝ)) := by
    simpa only [hχb] using hχderiv.continuousAt.tendsto
  refine ⟨φ ∘ χ, ?_, ?_, ?_⟩
  · change φ (χ b) = C b
    rw [hχb]
    exact hφ
  · apply ((eventually_gt_nhds hcb).and (hχtendsto.eventually hupper)).mono
    intro r hr
    have hratio : 0 < (r - c) / (b - c) := div_pos (sub_pos.mpr hr.1) hbc
    have hinverse : c + Real.exp (χ r) * (b - c) = r := by
      dsimp only [χ]
      rw [Real.exp_log hratio, div_mul_cancel₀ _ hbc0]
      ring
    simpa only [hinverse, Function.comp_apply] using hr.2
  · have hderiv := hφderiv.comp_of_eq b hχderiv hχb.symm
    have hcoeff : ((b - c) * d) * (b - c)⁻¹ = d := by
      rw [mul_right_comm, mul_inv_cancel₀ hbc0, one_mul]
    rw [hcoeff] at hderiv
    exact hderiv

end DifferentialGeometry.Analysis.Calculus
