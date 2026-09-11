import DifferentialGeometry.Analysis.Calculus.Periodic.Affine
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue



noncomputable section

open Function
open scoped ContDiff NNReal

namespace DifferentialGeometry.Analysis



theorem deriv_affinePeriodic {ψ : ℝ → ℝ} (hp : ∀ t, ψ (t + 1) = ψ t + 1) :
    Periodic (deriv ψ) 1 := by
  intro t
  have h := congrArg (fun f : ℝ → ℝ => deriv f t) (funext hp)
  simpa only [deriv_comp_add_const, deriv_add_const] using h



theorem exists_lipschitz_affinePeriodic {ψ : ℝ → ℝ} (hc : ContDiff ℝ 1 ψ)
    (hp : ∀ t, ψ (t + 1) = ψ t + 1) : ∃ C : ℝ≥0, LipschitzWith C ψ := by
  obtain ⟨B, hB, hb⟩ := exists_bound_of_continuous_unit_periodic
    (hc.continuous_deriv le_rfl) (deriv_affinePeriodic hp)
  refine ⟨⟨B, hB.le⟩, lipschitzWith_of_nnnorm_deriv_le (hc.differentiable one_ne_zero) ?_⟩
  intro x
  exact_mod_cast hb x

end DifferentialGeometry.Analysis
