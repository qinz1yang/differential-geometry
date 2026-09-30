import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjection
import DifferentialGeometry.Analysis.Calculus.CircleResolvent

set_option autoImplicit false

noncomputable section

open Complex Metric

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem ContDiffOn.starProjection_eigenspace_ball
    {f : E → H →L[ℂ] H} {s : Set E} {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n f s) (hself : ∀ x ∈ s, (f x).toLinearMap.IsSymmetric)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hc : ∀ x ∈ s, sphere c r ⊆ resolventSet ℂ (f x)) :
    ContDiffOn ℝ n (fun x =>
      (⨆ μ ∈ ball c r, Module.End.eigenspace (f x).toLinearMap μ).starProjection) s := by
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  have hi := hf.circleIntegral_resolvent c r (by simpa only [abs_of_nonneg hr] using hc)
  have hj := hi.const_smul ((2 * ↑Real.pi * I : ℂ)⁻¹)
  apply hj.congr
  intro x hx
  exact (ContinuousLinearMap.circleIntegral_resolvent_eq_starProjection
    (f x) (hself x hx) hr (hc x hx)).symm
