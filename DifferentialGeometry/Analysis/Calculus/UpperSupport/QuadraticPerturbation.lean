import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.MetricSpace.Lipschitz


noncomputable section

open Filter Set
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis

theorem deriv_deriv_add_mul_sq {φ : ℝ → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (Q : ℝ) :
    deriv (deriv (fun r => φ r + Q * r ^ 2)) 0 = deriv (deriv φ) 0 + 2 * Q := by
  have hquadratic (r : ℝ) : HasDerivAt (fun s : ℝ => Q * s ^ 2) (Q * (2 * r)) r := by
    simpa using
      ((hasDerivAt_id r).pow 2).const_mul Q
  have hfirst : deriv (fun r => φ r + Q * r ^ 2) =ᶠ[𝓝 (0 : ℝ)]
      (fun r => deriv φ r + Q * (2 * r)) := by
    filter_upwards [hφ.eventually (by norm_num)] with r hr
    exact ((hr.differentiableAt (by norm_num)).hasDerivAt.add (hquadratic r)).deriv
  rw [hfirst.deriv_eq]
  have hφ' : DifferentiableAt ℝ (deriv φ) 0 :=
    (hφ.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hlinear : HasDerivAt (fun r : ℝ => Q * (2 * r)) (2 * Q) 0 := by
    simpa only [id_eq, mul_one, mul_comm Q 2] using
      ((hasDerivAt_id (0 : ℝ)).const_mul 2).const_mul Q
  exact (hφ'.hasDerivAt.add hlinear).deriv

theorem upper_support_add_mul_sq_of_dist_le
    {M : Type*} [PseudoMetricSpace M] {f : M → ℝ} {s : Set M} {L : ℝ≥0}
    (hf : LipschitzOnWith L f s) {β γ : ℝ → M} {φ : ℝ → ℝ} {C D : ℝ}
    (hcenter : β 0 = γ 0)
    (hmem : ∀ᶠ r in 𝓝 (0 : ℝ), β r ∈ s ∧ γ r ∈ s)
    (hdeviation : ∀ᶠ r in 𝓝 (0 : ℝ), dist (β r) (γ r) ≤ C * r ^ 2)
    (hφ : ContDiffAt ℝ 2 φ 0) (htouch : φ 0 = f (γ 0))
    (hupper : (fun r => f (γ r)) ≤ᶠ[𝓝 (0 : ℝ)] φ)
    (hsecond : deriv (deriv φ) 0 ≤ D) :
    ContDiffAt ℝ 2 (fun r => φ r + ((L : ℝ) * C) * r ^ 2) 0 ∧
      (φ 0 + ((L : ℝ) * C) * (0 : ℝ) ^ 2 = f (β 0)) ∧
      ((fun r => f (β r)) ≤ᶠ[𝓝 (0 : ℝ)]
        (fun r => φ r + ((L : ℝ) * C) * r ^ 2)) ∧
      deriv (deriv (fun r => φ r + ((L : ℝ) * C) * r ^ 2)) 0 ≤
        D + 2 * (L : ℝ) * C := by
  refine ⟨hφ.add (by fun_prop), ?_, ?_, ?_⟩
  · simpa only [zero_pow two_ne_zero, mul_zero, add_zero, hcenter] using htouch
  · filter_upwards [hmem, hdeviation, hupper] with r hr hdev hup
    have hdiff : f (β r) - f (γ r) ≤ (L : ℝ) * dist (β r) (γ r) :=
      (le_abs_self _).trans (by
        simpa only [Real.dist_eq] using hf.dist_le_mul (β r) hr.1 (γ r) hr.2)
    have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_left hdev L.coe_nonneg)
    calc
      f (β r) ≤ f (γ r) + (L : ℝ) * (C * r ^ 2) := by linarith
      _ ≤ φ r + (L : ℝ) * (C * r ^ 2) := by linarith only [hup]
      _ = φ r + ((L : ℝ) * C) * r ^ 2 := by ring
  · rw [deriv_deriv_add_mul_sq hφ]
    nlinarith only [hsecond]

end DifferentialGeometry.Analysis
