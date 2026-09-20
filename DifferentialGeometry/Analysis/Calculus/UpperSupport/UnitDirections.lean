import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv


noncomputable section

open Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem deriv_deriv_comp_mul_left (φ : ℝ → ℝ) (c r : ℝ) :
    deriv (deriv (fun s => φ (c * s))) r = c ^ 2 * deriv (deriv φ) (c * r) := by
  have hfirst : deriv (fun s => φ (c * s)) = fun s => c * deriv φ (c * s) := by
    funext s
    simpa only [smul_eq_mul] using deriv_comp_mul_left c φ s
  rw [hfirst, deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul]
  ring

theorem exists_affine_upper_support_of_unit_directions
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {v : E} {D : ℝ}
    (hunit : ∀ u : E, ‖u‖ = 1 → ∃ φ : ℝ → ℝ,
      ContDiffAt ℝ 2 φ 0 ∧ φ 0 = f v ∧
      (fun r => f (v + r • u)) ≤ᶠ[𝓝 (0 : ℝ)] φ ∧
      deriv (deriv φ) 0 ≤ D) (w : E) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = f v ∧
      (fun r => f (v + r • w)) ≤ᶠ[𝓝 (0 : ℝ)] ψ ∧
      deriv (deriv ψ) 0 ≤ D * ‖w‖ ^ 2 := by
  by_cases hw : w = 0
  · refine ⟨fun _ => f v, contDiffAt_const, rfl, ?_, ?_⟩
    · exact Eventually.of_forall fun r => by simp only [hw, smul_zero, add_zero, le_refl]
    · simp [hw]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let u : E := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hwpos.ne']
  obtain ⟨φ, hφ, hzero, hupper, hsecond⟩ := hunit u hu
  have hc : ContDiffAt ℝ 2 (fun r : ℝ => ‖w‖ * r) 0 :=
    by simpa only [id_eq] using contDiffAt_const.mul contDiffAt_id
  have htendsto : Tendsto (fun r : ℝ => ‖w‖ * r) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using hc.continuousAt.tendsto
  refine ⟨fun r => φ (‖w‖ * r), ?_, ?_, ?_, ?_⟩
  · have hφc : ContDiffAt ℝ 2 φ (‖w‖ * 0) := by simpa only [mul_zero] using hφ
    exact hφc.comp 0 hc
  · simpa only [mul_zero] using hzero
  · filter_upwards [htendsto.eventually hupper] with r hr
    have hline : (‖w‖ * r) • u = r • w := by
      dsimp only [u]
      rw [smul_smul]
      congr 1
      field_simp [hwpos.ne']
    simpa only [hline] using hr
  · rw [deriv_deriv_comp_mul_left, mul_zero]
    nlinarith only [mul_le_mul_of_nonneg_left hsecond (sq_nonneg ‖w‖)]

end DifferentialGeometry.Analysis
