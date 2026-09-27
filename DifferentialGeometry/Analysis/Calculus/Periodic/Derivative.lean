import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import DifferentialGeometry.Analysis.Calculus.Periodic.Affine
import Mathlib.Algebra.Field.Periodic
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

open Set

namespace Function.Periodic

theorem fderiv
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {c : E} (hf : Function.Periodic f c) :
    Function.Periodic (_root_.fderiv 𝕜 f) c := by
  intro x
  rw [← fderiv_comp_add_right]
  exact congrArg (fun g : E → F => _root_.fderiv 𝕜 g x) (funext hf)

theorem lipschitzWith_of_norm_fderiv_le_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {c : ℝ} (hp : Function.Periodic f c) (hc : 0 < c)
    (hf : Differentiable ℝ f) {L : NNReal}
    (hbound : ∀ x ∈ Icc (0 : ℝ) c, ‖_root_.fderiv ℝ f x‖ ≤ (L : ℝ)) :
    LipschitzWith L f := by
  apply lipschitzWith_of_nnnorm_fderiv_le hf
  intro x
  obtain ⟨y, hy, hxy⟩ := (hp.fderiv (𝕜 := ℝ)).exists_mem_Ico₀ hc x
  rw [hxy]
  exact_mod_cast hbound y ⟨hy.1, hy.2.le⟩

end Function.Periodic

namespace Function.Periodic

theorem iteratedFDeriv
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {c : E} (hf : Function.Periodic f c) (n : ℕ) :
    Function.Periodic (_root_.iteratedFDeriv 𝕜 n f) c := by
  intro x
  rw [← iteratedFDeriv_comp_add_right n c x]
  exact congrArg (fun g : E → F => _root_.iteratedFDeriv 𝕜 n g x) (funext hf)

end Function.Periodic
