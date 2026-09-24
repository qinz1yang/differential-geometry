import DifferentialGeometry.Analysis.Calculus.Derivative.QuadraticDeviation
import DifferentialGeometry.Analysis.Calculus.UpperSupport.QuadraticPerturbation


noncomputable section

open Filter Set
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_affine_upper_support_of_curve_upper_support
    {f : E → ℝ} {s : Set E} {L : ℝ≥0} (hf : LipschitzOnWith L f s)
    {v w : E} (hs : s ∈ 𝓝 v) {γ : ℝ → E} {φ : ℝ → ℝ} {C D : ℝ}
    (hγ : ContDiffAt ℝ 2 γ 0) (hvalue : γ 0 = v) (hvelocity : deriv γ 0 = w)
    (hacceleration : ‖deriv (deriv γ) 0‖ ≤ C * ‖w‖ ^ 2)
    (hφ : ContDiffAt ℝ 2 φ 0) (htouch : φ 0 = f (γ 0))
    (hupper : (fun r => f (γ r)) ≤ᶠ[𝓝 (0 : ℝ)] φ)
    (hsecond : deriv (deriv φ) 0 ≤ D * ‖w‖ ^ 2) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = f v ∧
      (fun r => f (v + r • w)) ≤ᶠ[𝓝 (0 : ℝ)] ψ ∧
      deriv (deriv ψ) 0 ≤ (D + 2 * (L : ℝ) * (C + 1)) * ‖w‖ ^ 2 := by
  by_cases hw : w = 0
  · refine ⟨fun _ => f v, contDiffAt_const, rfl, ?_, ?_⟩
    · exact Eventually.of_forall fun r => by simp only [hw, smul_zero, add_zero, le_refl]
    · simp [hw]
  · have hdeviation : ∀ᶠ r in 𝓝 (0 : ℝ),
        dist (v + r • w) (γ r) ≤ ((C + 1) * ‖w‖ ^ 2) * r ^ 2 := by
      simpa only [dist_eq_norm, norm_sub_rev] using
        eventually_norm_sub_affine_le_of_second_deriv_bound_at_zero
          hγ hw hvalue hvelocity hacceleration
    have hline : ContinuousAt (fun r : ℝ => v + r • w) 0 := by fun_prop
    have hlineMem : ∀ᶠ r in 𝓝 (0 : ℝ), v + r • w ∈ s :=
      hline.preimage_mem_nhds (by simpa only [zero_smul, add_zero] using hs)
    have hγMem : ∀ᶠ r in 𝓝 (0 : ℝ), γ r ∈ s :=
      hγ.continuousAt.preimage_mem_nhds (by simpa only [hvalue] using hs)
    obtain ⟨hψ, hψtouch, hψupper, hψsecond⟩ :=
      upper_support_add_mul_sq_of_dist_le hf
        (by simpa only [zero_smul, add_zero] using hvalue.symm)
        (hlineMem.and hγMem) hdeviation hφ htouch hupper hsecond
    refine ⟨_, hψ, ?_, hψupper, ?_⟩
    · simpa only [zero_smul, add_zero] using hψtouch
    · convert hψsecond using 1; ring

end DifferentialGeometry.Analysis
