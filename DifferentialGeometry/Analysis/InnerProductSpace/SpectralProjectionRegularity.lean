import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjection
import DifferentialGeometry.Analysis.Calculus.CircleResolvent

set_option autoImplicit false

noncomputable section

open Complex Metric
open scoped NNReal Topology

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

theorem DifferentiableAt.norm_fderiv_starProjection_eigenspace_ball_le
    {f : E → H →L[ℂ] H} {x : E} (hf : DifferentiableAt ℝ f x)
    (hself : ∀ᶠ y in 𝓝 x, (f y).toLinearMap.IsSymmetric)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hc : sphere c r ⊆ resolventSet ℂ (f x)) (K : ℝ≥0)
    (hK : ∀ z ∈ sphere c r, ‖_root_.resolvent (f x) z‖ ≤ K) :
    ‖fderiv ℝ (fun y =>
      (⨆ μ ∈ ball c r, Module.End.eigenspace (f y).toLinearMap μ).starProjection) x‖ ≤
      r * (K : ℝ) ^ 2 * ‖fderiv ℝ f x‖ := by
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  have hc' : sphere c |r| ⊆ resolventSet ℂ (f x) := by simpa only [abs_of_nonneg hr] using hc
  have hn := hf.continuousAt.eventually
    ((isOpen_setOf_circle_subset_resolventSet c r).mem_nhds hc')
  have heq : (fun y =>
      (⨆ μ ∈ ball c r, Module.End.eigenspace (f y).toLinearMap μ).starProjection)
      =ᶠ[𝓝 x] (fun y => (2 * ↑Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, r), _root_.resolvent (f y) z)) := by
    filter_upwards [hself, hn] with y hy hcy
    exact (ContinuousLinearMap.circleIntegral_resolvent_eq_starProjection (f y) hy hr
      (by simpa only [abs_of_nonneg hr] using hcy)).symm
  rw [heq.fderiv_eq]
  simpa only [abs_of_nonneg hr] using hf.norm_fderiv_normalized_circleIntegral_resolvent_le
    c r hc' K (by simpa only [abs_of_nonneg hr] using hK)

theorem ContDiffOn.norm_iteratedFDeriv_starProjection_eigenspace_ball_le
    {U : Set E} (hU : IsOpen U) {f : E → H →L[ℂ] H} {m : ℕ}
    (hf : ContDiffOn ℝ m f U) (hself : ∀ y ∈ U, (f y).toLinearMap.IsSymmetric)
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hc : ∀ y ∈ U, sphere c r ⊆ resolventSet ℂ (f y))
    {x : E} (hx : x ∈ U) {δ σ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hσ : 0 ≤ σ)
    (K B : ℝ≥0) (hK : ∀ z ∈ sphere c r, ‖_root_.resolvent (f x) z‖ ≤ K)
    (hD : ∀ j, 1 ≤ j → j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ δ * B * σ ^ j) :
    ∀ n, 1 ≤ n → n ≤ m →
      ‖iteratedFDeriv ℝ n (fun y =>
        (⨆ μ ∈ ball c r, Module.End.eigenspace (f y).toLinearMap μ).starProjection) x‖ ≤
        r * δ * resolventDerivativeBound K B n * σ ^ n := by
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  have heq : Set.EqOn (fun y =>
      (⨆ μ ∈ ball c r, Module.End.eigenspace (f y).toLinearMap μ).starProjection)
      (fun y => (2 * ↑Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), _root_.resolvent (f y) z)) U := by
    intro y hy
    exact (ContinuousLinearMap.circleIntegral_resolvent_eq_starProjection (f y)
      (hself y hy) hr (hc y hy)).symm
  intro n hn hnm
  rw [← iteratedFDerivWithin_of_isOpen n hU hx, iteratedFDerivWithin_congr heq hx n,
    iteratedFDerivWithin_of_isOpen n hU hx]
  simpa only [abs_of_nonneg hr] using hf.norm_iteratedFDeriv_normalized_circleIntegral_resolvent_le
    hU c r (by simpa only [abs_of_nonneg hr] using hc) hx hδ hδ1 hσ K B
    (by simpa only [abs_of_nonneg hr] using hK) hD n hn hnm
