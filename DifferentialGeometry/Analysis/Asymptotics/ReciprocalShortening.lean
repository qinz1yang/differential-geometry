import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.ShortenedAngleLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp

open Filter
open scoped Topology

namespace Real

theorem tendsto_sqrt_mul_reciprocal_div_atTop {σ : ℕ → ℝ} {C : ℝ}
    (hC : 0 < C) (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun i => sqrt (σ i) * ((σ i)⁻¹ / C)) atTop atTop := by
  have hroot : Tendsto (fun i => sqrt (σ i)) atTop (𝓝 0) := by simpa using hσ.sqrt
  have hwithin : Tendsto (fun i => sqrt (σ i)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hroot, Eventually.of_forall fun i => sqrt_pos.mpr (hσpos i)⟩
  have hh := (tendsto_inv_nhdsGT_zero.comp hwithin).atTop_div_const hC
  have heq (i : ℕ) : sqrt (σ i) * ((σ i)⁻¹ / C) = (sqrt (σ i))⁻¹ / C := by
    have hsq : 0 < sqrt (σ i) := sqrt_pos.mpr (hσpos i)
    field_simp [hsq.ne', (hσpos i).ne', hC.ne']
    nlinarith [sq_sqrt (hσpos i).le]
  simpa only [Function.comp_def, heq] using hh

theorem tendsto_reciprocal_shortened_angle_lower_bound {σ : ℕ → ℝ} {C : ℝ}
    (hC : 0 < C) (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun i => 2 * arcsin (max 0 (sin ((Real.pi / 2 - σ i) / 2) -
      ((sin ((Real.pi / 2 - σ i) / 2))⁻¹ - sin ((Real.pi / 2 - σ i) / 2)) /
        (exp (2 * (sqrt (σ i) * ((σ i)⁻¹ / C))) - 1)))) atTop (𝓝 (Real.pi / 2)) := by
  apply tendsto_shortened_angle_lower_bound (by linarith [pi_pos]) (by linarith [pi_pos])
    (by simpa only [sub_zero] using tendsto_const_nhds.sub hσ)
  exact tendsto_sqrt_mul_reciprocal_div_atTop hC hσpos hσ

end Real
